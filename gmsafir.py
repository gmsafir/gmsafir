# coding: utf-8
import os
import gmsh
import math
import sys
import json
import ast
import time
from copy import deepcopy,copy
import re
import fortranformat as ff
from datetime import datetime
import numpy as np
from numpy import linalg as LA
import subprocess

class Myapp: # Use of class only in order to share 'params' as a global variable with the "event manager" below (not working properly without class)
    def __init__(self, parent=None):

        gmsh.initialize(sys.argv)

        self.version="2022-03-04 - Version 1.0(BETA)"
        self.authors="Univ. of Liege & Efectis France"

        # Symmetries and voids
        self.realsyms=0
        self.nvoids=0
        self.symvoids=0

        # Vars
        self.toClean={}
        self.removeStr="{}Remove"
        self.updateStr="{}Add-Update"
        self.drawStr="{}Draw Axes"
        self.legendtag=0

        #General Lists
        self.listMats=[]
        #
        self.listLAX=[]
        self.laxid=0
        self.LAXtag=1
        self.pointLAX=[]
        self.ViewFinalLAX=True
        self.ViewLAXOnce=True
        self.isViewLAX=False
        self.LAXspecial=False
        self.launchSAFIR=False

        self.SolidFilename="" # Global variable
        #
        self.permutespecial=False # will allow to monitor if the permutation comes for specialcase or not, important for the creation of GUI menus from the DB

        # Make other solver invisible
        for i in range(5):
            gmsh.option.setString('Solver.Name{}'.format(i), '')
        #
        self.allShapes=["Point","Curve","Surface","Volume"]

        # for subroutine CreatIN: Correspondence btw flag of elemType and number of nodes in the element
        self.allElemTypesNbNodes={15:1,1:2,2:3,3:4,4:4,5:8,6:6}
        #
        self.nopopup=False
        self.go_on=True
        #
        self.g4sfile=""
        self.g4sfileError=""
        self.geofile=""
        self.getCmdLine() # Interpret the command line parameters
        #
        if not self.go_on: #  Error found in the command line parameters
            gmsh.finalize()
            sys.exit(127)
        
        # specialCategs is defined by default - will be updated in getG4sJson if g4sfile exists:    
        self.specialCategs=[('Beam Section Type','mats',1,'more'),('Truss Section Type','mats',1,'one'),('Surface Material','mats',2,'one'), \
                            ('Volume Material','mats',3,'one'),('Solid Material','mats',3,'more')]
        #
        # Reading the different DBs:
        #
        # ContexDB: internal json object in this script.
        # to allow the on-the-fly creation of menus in the Drawing Window, this creation being based on the events caught by the "event manager".
        # ContextDB is easier to modify and explore than the ONELAB.json object, since being defined as a tree with branches and leaves (see at the quasi end of this script).
        # This latter is only used in the menus.
        #
        # SafirDB: internal json object in this script,
        # containing the general information for the on-the-fly creation of menus in the Left Window.
        #
        # InspectDB: internal json object in this script
        # contains the information for the object Inspector (essentially pushButtons in the Left Window, to request current view on the objects defined in the Drawing Window)
        #
        # Read InspectDB
        self.inspectDB=json.loads(inspectDBstring)
        #
        # Keep track of the default ContextDB from this script, with default values
        self.contextDB0=json.loads(contextDBstring)
        self.initCompleteContextDB(self.contextDB0)

        # Retrieve initial version of ContextDB
        if(os.path.exists(self.g4sfile)): # load ContextDB from existing file
            #
            self.contextDB=json.loads(contextDBstring) # load ContextDB from this script
            self.initCompleteContextDB(self.contextDB) # Copy Materials: same for Volume/th3D than Surface/th2D
            self.safirDB=json.loads(safirDBstring)
            self.initCompleteSafirDB(self.safirDB)
            #
            self.getG4sJson(self.g4sfile) # if existing DB in input directory
            #
        else:
            self.contextDB=json.loads(contextDBstring) # load ContextDB from this script
            self.initCompleteContextDB(self.contextDB) # Copy Materials: same for Volume/th3D than Surface/th2D
            self.safirDB=json.loads(safirDBstring)
            self.initCompleteSafirDB(self.safirDB)
            self.pbType="Thermal 2D" #Initialization of problem type

        self.isThermal="Thermal" in self.pbType

        if(self.nopopup): # Batch mode
            return

       # GUI Mode: Initial load the GUI's menus
        gmsh.onelab.clear()
        #
        self.updateGeneralLists()
        self.loadContextDB(self.contextDB,self.pbType,True)
        self.loadSafirDB()
        self.loadInspectDB(self.pbType)
        s=deepcopy(json.loads(gmsh.onelab.get().replace("\\","/"))["onelab"]["parameters"])
        self.params= [k for k in s if 'SAFIR' in k['name'] or self.pbType in k['name']]


    # Complete automatically some repetitive pieces in ContextDB, at initialization step when load from default values in this script
    def initCompleteContextDB(self,tmpg0):
        # Copy the Surface Materials from Thermal2D into Thermal3D
        tmp1=self.getDBValue(tmpg0,[("children","name","Surface"),("children","name","Thermal 2D"),("children","name","New Material Definition")],False)['children']
        tmp2=self.getDBValue(tmpg0,[("children","name","Volume"),("children","name","Thermal 3D"),("children","name","New Material Definition")],False)['children']
        for i in range(len(tmp1)):
            itmp=tmp1[i]
            tmp2.append(deepcopy(itmp))
        #
        # Remove from Thermal3D the Young module and Poisson coefficient
        tmp2=self.getDBValue(tmpg0,[("children","name","Volume"),("children","name","Thermal 3D"),("children","name","New Material Definition")],False)
        rc=self.recursActionContextDB(tmp2,'cut',['Young module','Poisson coefficient'])
        #
        #Copy the Curve and Surface Materials from Struct2D into Struc3D
        tmp1=self.getDBValue(tmpg0,[("children","name","Curve"),("children","name","Structural 2D"),("children","name","New Material Definition")],False)['children']
        tmp2=self.getDBValue(tmpg0,[("children","name","Curve"),("children","name","Structural 3D"),("children","name","New Material Definition")],False)['children']
        for i in range(len(tmp1)):
            itmp=tmp1[i]
            tmp2.append(deepcopy(itmp))
        #
        tmp1=self.getDBValue(tmpg0,[("children","name","Surface"),("children","name","Structural 2D"),("children","name","New Material Definition")],False)['children']
        tmp2=self.getDBValue(tmpg0,[("children","name","Surface"),("children","name","Structural 3D"),("children","name","New Material Definition")],False)['children']
        for i in range(len(tmp1)):
            itmp=tmp1[i]
            tmp2.append(deepcopy(itmp))
        #
        #Add Material Names to Thermal2D and Thermal3D
        tmp2=self.getDBValue(tmpg0,[("children","name","Surface"),("children","name","Thermal 2D"),("children","name","New Material Definition")],False)
        rc=self.recursActionContextDB(tmp2,'add_name_mat mat',[])
        tmp2=self.getDBValue(tmpg0,[("children","name","Volume"),("children","name","Thermal 3D"),("children","name","New Material Definition")],False)
        rc=self.recursActionContextDB(tmp2,'add_name_mat mat',[])
        #
        #Add Material Names to Struct2D and Struct3D
        tmp2=self.getDBValue(tmpg0,[("children","name","Curve"),("children","name","Structural 2D"),("children","name","New Material Definition")],False)
        rc=self.recursActionContextDB(tmp2,'add_name_mat mat',[])
        tmp2=self.getDBValue(tmpg0,[("children","name","Curve"),("children","name","Structural 3D"),("children","name","New Material Definition")],False)
        rc=self.recursActionContextDB(tmp2,'add_name_mat mat',[])
        tmp2=self.getDBValue(tmpg0,[("children","name","Surface"),("children","name","Structural 2D"),("children","name","New Material Definition")],False)
        rc=self.recursActionContextDB(tmp2,'add_name_mat mat',[])
        tmp2=self.getDBValue(tmpg0,[("children","name","Surface"),("children","name","Structural 3D"),("children","name","New Material Definition")],False)
        rc=self.recursActionContextDB(tmp2,'add_name_mat mat',[])
        tmp2=self.getDBValue(tmpg0,[("children","name","Volume"),("children","name","Structural 3D"),("children","name","New Material Definition")],False)
        rc=self.recursActionContextDB(tmp2,'add_name_mat mat',[])

        #Add LAX Names to Struct2D and Struct3D
        #tmp2=self.getDBValue(tmpg0,[("children","name","Curve"),("children","name","Structural 2D"),("children","name","New LAX Definition")],False)
        #rc=self.recursActionContextDB(tmp2,'add_name_lax lax',[])
        tmp2=self.getDBValue(tmpg0,[("children","name","Curve"),("children","name","Structural 3D"),("children","name","New LAX Definition")],False)
        rc=self.recursActionContextDB(tmp2,'add_name_lax lax',[])


    #Perform different actions recursively in the leaves of ContextDB: 'find_path_to_name', 'list_names', 'filefor', 'cut', 'add_name', 'permute_simple'
    def recursActionContextDB(self,tmpg,acttype,listprops):
         #

         if('find_path_to_name'in acttype):
             rc=[]
             if(listprops is None):
                 listprops=[]
             listprops.append(tmpg['name'])
         elif('list_names' in acttype):
             tmplst=acttype.split('/')
             if(len(tmplst)>1):
                 act0,pref=tmplst
                 suff=pref+"-"+tmpg['name']
                 acttype=act0+"/"+suff
             else:
                 act0=acttype
                 suff=tmpg['name']
                 acttype=act0+"/"+suff
             #
             rc=0

         else:
             rc=0

         if(tmpg['children']==[]): # Select the leaves in the DB
            #
            if('filefor' in acttype):
                props=tmpg["props"]
                for k in range(len(props)):
                    iprop=props[k]
                    if 'name' in iprop and not 'File for' in iprop['name']:
                        if('valueLabels' in iprop and 'User-defined' in list(iprop['valueLabels'].keys())):
                            pattern=re.compile("^[0-9]+")
                            str0=re.search(pattern,iprop['name']).group(0)
                            propnam=iprop['name'].replace(str0,'')
                            j=[j0 for j0 in range(len(props)) if 'name' in props[j0] and 'File for '+propnam in props[j0]['name']][0]
                            ival=iprop['values'][0]
                            ikey=[k0 for k0,v0 in iprop['valueLabels'].items() if v0==ival][0]
                            if(ikey=="User-defined"):
                                tmpg["props"][j]['visible']=True
                            else:
                                tmpg["props"][j]['visible']=False


            elif('find_path_to_name' in acttype):
                _,inam0,ivlstr=acttype.split("/")
                ik=[k for k in range(len(tmpg["props"])) if not 'name' in tmpg["props"][k]][0]
                ifound=False
                for ikey in ['ents','pgs']:
                 #for ikey in ['ents']:
                     tmp1keys=tmpg["props"][ik][ikey]
                     #
                     if(tmp1keys!={}):
                         for inb in sorted(tmp1keys):
                             ivl=[k for k in tmp1keys[inb] if list(k.keys())[0]==inam0][0][inam0][0]
                             if(ivl==ivlstr):
                                ifound=True
                if(ifound):
                    listprops.append('True')
                else:
                    listprops.append('False')
                rc.append(listprops)

            elif(acttype=='cut'): # Remove a list of parameters in the property
                 k=0
                 while(k<len(tmpg["props"])):
                     tmp1=tmpg["props"][k]
                     if 'name' in tmp1:
                         inam=copy(tmp1['name'])
                         #
                         found=False
                         for ilist in listprops:
                             if ilist in inam and not found:
                                 found=True
                         if(found):
                             tmpg["props"].remove(tmp1)
                         else:
                             k+=1
                         #
                     else:
                         k+=1

            #
            elif('add_name' in acttype): # Add a Material name
                 pref,suff=acttype.split(" ")
                 _,_,imatlax=pref.split("_")
                 #
                 if(imatlax=="mat"):
                     inam0="New Material Name"
                 elif(imatlax=="lax"):
                     inam0="New LAX Name"
                 #
                 tmpg['props'].append({"name":inam0,"type":"string","values":[suff]})
            #
            elif('list_names' in acttype): # List the materials
                 _,suff=acttype.split("\t")
                 _,ityp=suff.split(";")

                 if("mat" in suff):
                     inam0='New Material Name'
                 elif("lax" in suff):
                     inam0='New LAX Name'
                 #Special field
                 foundtors=False
                 tab0=[k for k in range(len(tmpg["props"])) if 'HIDDEN torsname' in list(tmpg["props"][k].values())]
                 if(tab0!=[]):
                     ik=tab0[0]
                     torsname=tmpg["props"][ik]["values"][0]
                     foundtors=True
                 #
                 ik=[k for k in range(len(tmpg["props"])) if not 'name' in tmpg["props"][k]][0]  #look for pgs/ents in the leaf
                 #
                 for ikey in ['ents','pgs']:
                     tmp1keys=tmpg["props"][ik][ikey]
                     #
                     if(tmp1keys!={}):
                         for inb in sorted(tmp1keys):
                             print("list_names:",tmp1keys[inb])
                             print('list_names:',inam0,[k for k in tmp1keys[inb] if list(k.keys())[0]==inam0][0][inam0])
                             ivl=[k for k in tmp1keys[inb] if list(k.keys())[0]==inam0][0][inam0][0]
                             j=[k for k in listprops if list(k.keys())[0]==ivl+";"+ityp]
                             if(j==[]):
                                if foundtors:
                                     dict0=json.loads("""{"torsname":[" """+torsname+""" "]}""")
                                     tkey=deepcopy(tmp1keys[inb])
                                     tkey.append(dict0)
                                     listprops.append({ivl+";"+ityp:tkey})
                                     #foundtors=False
                                else:
                                    tkey0=deepcopy(tmp1keys[inb])
                                    for ik0 in range(len(tkey0)):
                                        knam=list(tkey0[ik0].keys())[0];v0=list(tkey0[ik0].values())[0]
                                        k1=[k for k in range(len(tmpg["props"])) if 'name' in tmpg["props"][k] and tmpg["props"][k]['name']==knam][0]
                                        if('valueLabels' in tmpg["props"][k1]):
                                            s0=[k for k,v in tmpg["props"][k1]['valueLabels'].items() if v==v0[0]][0]
                                            tkey0[ik0][knam]=[s0]
                                        #tkey0[ik0]

                                    listprops.append({ivl+";"+ityp:tkey0})
         #
         else: #Select the branches in the DB
            #
            if("permute_simple" in acttype): # Recursion only on the first child
                _,inam0=acttype.split("\t")
                #
                idx=[k for k in range(len(tmpg['children'])) if tmpg['children'][k]['name']==listprops[0]][0]
                #
                if(idx!=0):
                    tmpg['children'][idx],tmpg['children'][0]=tmpg['children'][0],tmpg['children'][idx]
                #
                if(idx==0 and len(listprops)==2): # Means that the pg and/or ent is not in first position of the last leaf in ContextDB: need to permute the values, keeping the same order for the keys
                    matlaxnam=listprops[1]
                    ik=[k for k in range(len(tmpg['children'][0]["props"])) if not 'name' in tmpg['children'][0]["props"][k]][0] #look for pgs/ents in the leaf
                    #
                    i=0
                    for ikey in ['ents','pgs']:
                        tmp1keys=tmpg['children'][0]["props"][ik][ikey]
                        for km in range(len(sorted(tmp1keys))):
                            inb=sorted(tmp1keys)[km]
                            if(i==0):
                                k0=km
                                inb0=inb
                                ikey0=ikey
                            i+=1
                            k1tab=[k for k in tmp1keys[inb] if list(k.keys())[0]==inam0 and list(k.values())[0][0]==matlaxnam]
                            if(k1tab!=[]):
                                k1=km
                                inb1=inb
                                ikey1=ikey
                    # Permutation:
                    tmpg['children'][0]["props"][ik][ikey0][inb0],tmpg['children'][0]["props"][ik][ikey1][inb1]=tmpg['children'][0]["props"][ik][ikey1][inb1],tmpg['children'][0]["props"][ik][ikey0][inb0]
                    #
                newidx=0
                listprops.remove(listprops[0])
                rc=self.recursActionContextDB(tmpg["children"][newidx],acttype,listprops)
            #
            else: # Recursion on all children
                for newidx in range(len(tmpg['children'])):
                    if("find_path_to_name" in acttype):
                        rc.extend(self.recursActionContextDB(tmpg["children"][newidx],acttype,listprops[:]))
                    #
                    else:
                        rc=self.recursActionContextDB(tmpg["children"][newidx],acttype,listprops)
            #
         return rc


    def initCompleteSafirDB(self,tmpg0):
        #  Copy all Struct2D props and children into Struct3D
        tmp1=self.getDBValue(tmpg0,[("children","name","Structural 2D")],False)
        tmp2=self.getDBValue(tmpg0,[("children","name","Structural 3D")],False)
        #
        for i in range(len(tmp1['children'])):
            itmp=deepcopy(tmp1['children'][i])
            tmp2['children'].append(itmp)
        #
        for i in range(len(tmp1['props'])):
            itmp=deepcopy(tmp1['props'][i])
            tmp2['props'].append(itmp)

        tmp2['props'].append({"name":"NG SHELLTHICK","type":"number","values":[0],"min":0,"max":20,"step":0})
        tmp2['props'].append({"name":"NG SOLID","type":"number","values":[0],"min":0,"max":20,"step":0})



    def getCmdLine(self):
        msg0=""""
            Correct syntax is one of these options:
            1/ GUI mode in current directory: python g4s.py
            2/ GUI mode: python g4s.py [file name of a GEO file (fullpath)]
            3/ GUI mode: python g4s.py [directory name containing 0 or 1 GEO file]
            4/ Batch mode: python g4s.py [directory name containing 1 or more GEO files] -nopopup
            """
        # Manage input file
        if len(sys.argv)==2:
            arg0=sys.argv[1]

            if("-help" in arg0):
                msg=""
                gmsh.logger.write(msg0, level="info")
                self.go_on=False
            #
            if(re.search('.geo$',arg0)!=None): #Input is suposed to be a GEO file
                self.geofile=arg0
                self.dir=os.path.dirname(self.geofile)
                if(os.path.exists(self.geofile)):
                    gmsh.logger.write("Ok, this .geo file does exist - The run directory is the directory containing this geofile", level="info")
                    gmsh.open(self.geofile)
                #
#                 else:
#                     gmsh.logger.write("GEO file doesn't exist yet", level="info")
#                     f=open(self.geofile,"w")
#                     f.write("SetFactory('OpenCASCADE');\n")
#                     f.close()

            #
            elif(os.path.isdir(arg0)): #input is supposed to be a directory
                self.dir=arg0
                # Get potential  GEO file
                tmpfiles=[k for k in os.listdir(arg0) if (re.search('.geo$',k)!=None)]
                if(tmpfiles!=[]): # there exists at least 1 GEO file
                    if(len(tmpfiles)==1):
                        gfile=tmpfiles[0]
                        self.geofile=os.path.join(self.dir,gfile)
                        gmsh.logger.write("Ok, found a single GEO file in this directory, "+os.path.basename(self.geofile)+" - It will be used", level="info")
                        gmsh.open(self.geofile)
                        #
                    elif(len(tmpfiles)>1):
                        msg="-- Too many GEO files in the directory - Need to specify one"
                        gmsh.logger.write(msg+"\n"+msg0, level="info")
#                         self.go_on=False
                #
                else: # no GEO file
                    gmsh.logger.write("No GEO file found in the directory", level="info")
#                     gfile="untitled.geo"
#                     self.geofile=os.path.join(self.dir,gfile)
#                     f=open(self.geofile,"w")
#                     f.write("SetFactory('OpenCASCADE');\n")
#                     f.close()
#                     gmsh.open(self.geofile)
                    #
            else:
                msg="""
                Input is neither a valid directory nor a GEO file
                """
                gmsh.logger.write(msg+"\n"+msg0, level="error")
                self.go_on=False
        #
        elif len(sys.argv)==1:
            #gmsh.logger.write("Start with no parameters", level="info")
            self.dir=os.getcwd()
            tmpfiles=[k for k in os.listdir(self.dir) if (re.search('.geo$',k)!=None)]
            if(tmpfiles!=[]): # there exists at least 1 GEO file
                if(len(tmpfiles)==1):
                    gfile=tmpfiles[0]
                    self.geofile=os.path.join(self.dir,gfile)
                    gmsh.logger.write("Ok, found a single GEO file in this directory, "+os.path.basename(self.geofile)+" - It will be used", level="info")
                    gmsh.open(self.geofile)
                    #
                elif(len(tmpfiles)>1):
                    msg="-- Too many GEO files in the directory - Need to specify one"
                    gmsh.logger.write(msg+"\n"+msg0, level="info")
#                     self.go_on=False
            #
            else: # no GEO file
                gmsh.logger.write("No GEO file found in the directory", level="info")
#                 gfile="untitled.geo"
#                 self.geofile=os.path.join(self.dir,gfile)
#                 f=open(self.geofile,"w")
#                 f.write("SetFactory('OpenCASCADE');\n")
#                 f.close()
#                 gmsh.open(self.geofile)
        #
        elif len(sys.argv)==3:
            arg0=sys.argv[1]
            arg1=sys.argv[2]
            if(arg1!="-nopopup" or (not os.path.isdir(arg0))):
                msg="-- Incorrect parameters in command line -- "
                gmsh.logger.write(msg+"\n"+msg0, level="error")
                self.go_on=False
            else:
                self.dir=arg0
                self.nopopup=True
        else:
            msg="-- Incorrect parameters in command line -- "
            gmsh.logger.write(msg+"\n"+msg0, level="error")
            self.go_on=False

        # Look for the G4S file and IN file
        if self.go_on:
            #gfile=os.path.basename(self.geofile)
            self.g4sfile=self.geofile.replace(".geo",".g4s")
            if(os.path.exists(self.g4sfile)):
                gmsh.logger.write("G4S file corresponding to this GEO file does already exist - It will be used", level="info")
            self.INfile=self.geofile.replace(".geo",".IN")
            if(os.path.exists(self.INfile)):
                gmsh.logger.write("SAFIR .IN file does exist - It will be overwritten when .IN file creation will be requested", level="warning")


    #Load ContextDB and SafirDB from the disk
    def getG4sJson(self,file0): # Name originates from the time where G4S file was a JSON format, no more the case
        #
        #file0="E:\Share\Efectis\SAFIR\GMSH\G4S\\first_case\debug_JMF_20220201\\test.txt"
        #
        # Read G4S file (no more a JSON format) and remove commented and empty lines (or full of whitespaces)
        with open(file0) as f:
            lines=f.readlines()
            pattern=re.compile("^#")
            pattern2=re.compile("^[\s]*$")
            #
            thelines=[]
            for iline in lines:
                if(re.search(pattern, iline)==None and re.search(pattern2, iline)==None and iline!="\n"):
                    thelines.append(iline.replace('\n',''))
        f.close()
        #
        # Retrieve the problem type and make permutation in safirDB and contextDB accordingly
        i0=[i for i in range(len(thelines)) if "Problem Type" in thelines[i]][0]
        iline0=thelines[i0]
        _,pbtyp=iline0.split(':')
        self.pbType=pbtyp.strip()

        if("3D" in self.pbType):
            self.specialCategs=[('Beam Section Type','mats',1,'more'),('Truss Section Type','mats',1,'one'),('Surface Material','mats',2,'one'), \
                            ('Shell Material','mats',2,'one'),('Shell Rebar','mats',1,'more'),('Volume Material','mats',3,'one'),('Solid Material','mats',3,'more'), \
                            ('Beam Section Local Axes','lax',1,'one')]
        else:
            self.specialCategs=[('Beam Section Type','mats',1,'more'),('Truss Section Type','mats',1,'one'),('Surface Material','mats',2,'one'), \
                            ('Volume Material','mats',3,'one'),('Solid Material','mats',3,'more')]

        #
        # Permute safirDB
        found=False
        endTree=False
        merror=""
        listRecurs=[{'key':"",'end_lvl':0}]
        inam="Problem Type"
        ivl=[1]
        ivlstr=self.pbType
        self.safirDB['children'],listRecurs,permute,found,endTree,merror=self.permuteDB(self.safirDB['children'],listRecurs,"",found,endTree,"-1",inam,ivl,ivlstr,999,merror)
        if(merror!=""):
            self.g4sfileError=merror
            gmsh.logger.write(".g4s file not loaded!!! "+merror, level="error")
            return
        #
        # Permute ContextDB
        found=False
        endTree=False
        merror=""
        listRecurs=[{'key':"",'end_lvl':0}]
        inam="Problem Type"
        ivl=[1]
        ivlstr=self.pbType
        self.contextDB['children'],listRecurs,permute,found,endTree,merror=self.permuteDB(self.contextDB['children'],listRecurs,"",found,endTree,"-1",inam,ivl,ivlstr,999,merror)
        if(merror!=""):
            self.g4sfileError=merror
            gmsh.logger.write(".g4s file not loaded!!! "+merror, level="error")
            return
        #
        thelines.remove(iline0)
        #

        # Function to change a key and/or property value: both are handled for safirDB by permuteDB (not the case for concreteDB)
        def changeSafirDBKeyAndProp(iprop,ival):
            found=False
            endTree=False
            merror=""
            listRecurs=[{'key':"",'end_lvl':0}]
            inam=iprop
            ivl=[ival]
            ivlstr=ival
            self.safirDB['children'],listRecurs,permute_safir,found,endTree,merror=self.permuteDB(self.safirDB['children'],listRecurs,"",found,endTree,"-1",inam,ivl,ivlstr,999,merror)
            if merror!="":
                self.g4sfileError=merror
                gmsh.logger.write(".g4s file not loaded!!! "+merror, level="error")
                return
        #
        #Reindex lines to account for bracketed props
        thelineswithprops=[]
        multi=False

        for iline in thelines:
            #
            pattern_beg=re.compile("=.*{.*$")
            pattern_end=re.compile("}.*$")
            #
            if(not multi and re.search(pattern_beg, iline)!=None):
                tmpl=[iline]
                multi=True
            #
            elif(not multi and re.search(pattern_end, iline)!=None):
                gmsh.logger.write(".g4s file not loaded!!! A block of properties is trying to close but was not started", level="error")
                self.g4sfileError="error"
                return
            #
            elif multi :
                if(re.search(pattern_beg, iline)!=None): #precedent brackets have not been closed, cannot start a new one
                    gmsh.logger.write(".g4s file not loaded!!! Last block of properties was not closed, cannot start a new one", level="error")
                    self.g4sfileError="error"
                    return
                #
                if(re.search(pattern_end, iline)!=None): # end of bracketed props
                    tmpl.append(iline)
                    multi=False
                    thelineswithprops.append(tmpl)
                    tmpl=[]
                else: # still in the bracketed props
                    tmpl.append(iline)
            #
            else: # multi=False and not(pattern_beg,pattern_end): correct single line
                thelineswithprops.append([iline])
        #
        if multi: #
            gmsh.logger.write(".g4s file not loaded!!! Last block of properties was not closed", level="error")
            self.g4sfileError="error"
            return
        #
        # Load information in safirDB and contextDB
        for iline in thelineswithprops:
            #
            # Evaluate if data in the line will belong to safirDB or to ContextDB
            isgen=True
            #
            for ishp in self.allShapes:
                pattern0=re.compile("^"+ishp)
                if(re.search(pattern0, iline[0])!=None):
                    isgen=False
            #
            if isgen: #safirDB
                #
                if(len(iline)==1): #changes in first-level properties
                    #
                    iprop,ival=iline[0].split(":");iprop=iprop.strip();ival=ival.strip()
                    tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType)],False)['props']
                    idxtab=[k for k in range(len(tmp0)) if tmp0[k]['name']==iprop]

                    #
                    if(idxtab!=[]): # is a SafirDB "prop"
                        k=idxtab[0]
                        tmp0=changeSafirDBKeyAndProp(iprop,ival)
                        #

                    else: # is a SafirDB "key"
                        tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType)],False)['children']
                        idxtab2=[k for k in range(len(tmp0)) if tmp0[k]['key']==iprop]
                        #
                        if(idxtab2!=[]): # is really a key- Permute
                            tmp0=changeSafirDBKeyAndProp(iprop,ival)
                        #
                        else: # is neither a "props" nor a "key"
                            gmsh.logger.write("Problem reading the .g4s file: \""+iprop+"\" is not recognized", level="error")
                            self.g4sfileError="error"
                            return
                #
                else: #changes in first-level key and second-level properties
                    #
                    #Treat line[0] as a safirDB "key"
                    #
                    iprop0,ival=iline[0].split(":");iprop0=iprop0.strip()
                    ival=re.sub(pattern_beg,"",ival).strip()
                    #
                    tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType)],False)['children']
                    idxtab2=[k for k in range(len(tmp0)) if tmp0[k]['key']==iprop0]
                    #
                    if(idxtab2!=[]): # is really a key- Permute
                        tmp0=changeSafirDBKeyAndProp(iprop0,ival)
                    #
                    else: # is neither a "props" nor a "key"
                        gmsh.logger.write("Problem reading the .g4s file: \""+iprop0+"\" is not recognized", level="error")
                        self.g4sfileError="error"
                        return
                    #
                    # Now treat the properties
                    for ik in range(1,len(iline)-1):
                        jline=iline[ik]
                        iprop,ival=jline.split(":");iprop=iprop.strip();ival=ival.strip()
                        tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","key",iprop0)],False)['props']
                        idxtab=[k for k in range(len(tmp0)) if tmp0[k]['name']==iprop]
                        #
                        if(idxtab!=[]): # is a SafirDB "prop"
                            k=idxtab[0]
                            tmp0=changeSafirDBKeyAndProp(iprop,ival)
                        else:
                            gmsh.logger.write("Problem reading the .g4s file: \""+iprop+"\" is not recognized", level="error")
                            self.g4sfileError="error"
                            return
            #
            else: # contextDB
                #
                # Differentiate btw delocalized properties (New Material/New LAX) and localized properties
                iline0=re.sub(pattern_beg,"",iline[0]).strip()
                #
                if(":" in iline0):
                    iprop0,ival0=iline0.split(":");iprop0=iprop0.strip();ival0=ival0.strip()
                else:
                    iprop0=iline0
                #
                ishp,inam0=iprop0.split('-');ishp=ishp.strip();inam0=inam0.strip()
                #
                if(inam0 == "New Material Definition" or inam0 == "New LAX Definition"): # delocalized properties
                    inam=inam0
                    ikey='ents'
                    inb=1
                #
                else: # localized properties
                    pattern_fct=re.compile("\((.)*\)$")
                    pattern_fct2=re.compile("^(.)*\((\w)*(\s)*(\w)*(\s)*")
                    pattern_fct3=re.compile("\)")
                    inam=re.sub(pattern_fct,"",inam0)
                    inb1=re.sub(pattern_fct2,"",inam0);inb=int(re.sub(pattern_fct3,"",inb1))
                    if("Physical" in inam0):
                        ikey='pgs'
                    else:
                        ikey='ents'
                #
                ishptot=ishp+" "+str(inb)
                if(ikey=='pgs'):
                    ishptot="Physical "+ishptot
                #
                pref_elem="ONELAB Context/"+ishptot+"/"+self.pbType+"/"+inam

                #
                if inam == "New Material Definition":
                    _,subnam=iline[1].split(":");subnam=subnam.strip()
                    _,typnam=iline[2].split(":");typnam=typnam.strip()
                    pref_elem+="/"+typnam+"/"+subnam
                    istart=3
                else:
                    pref_elem+="/-"
                    istart=1
                #
                #
                if inam=="New Material Definition":
                    # Need permutation of Material Type and then of Material Sub-Category
                    #
                    tmp0=self.getDBValue(self.contextDB,[("children","name",ishp),("children","name",self.pbType),("children","name",inam)],False)['children']
                    #
                    found=False
                    endTree=False
                    merror=""
                    listRecurs=[{'key':"",'end_lvl':0}]
                    levelChange=999
                    tmp0,listRecurs,permute,found,endTree,merror=self.permuteDB(tmp0,listRecurs,"",found,endTree,"-1","Material Type",[typnam],typnam,levelChange,merror)
                    #
                    tmp0=self.getDBValue(self.contextDB,[("children","name",ishp),("children","name",self.pbType),("children","name",inam),("children","name",typnam)],False)['children']
                    #
                    found=False
                    endTree=False
                    merror=""
                    listRecurs=[{'key':"",'end_lvl':0}]
                    levelChange=999
                    tmp0,listRecurs,permute,found,endTree,merror=self.permuteDB(tmp0,listRecurs,"",found,endTree,"-1","Material Sub-category",[subnam],subnam,levelChange,merror)
                    #
                if merror!="":
                    gmsh.logger.write(".g4s file not loaded!!! "+merror, level="error")
                    self.g4sfileError=merror
                    return
                #
                # Now updates
                toStore=[]
                #
                for ik in range(istart,len(iline)-1):
                    iprop,ival=iline[ik].split(":");iprop=iprop.strip();ival=ival.strip()
                    fullname=pref_elem+"/"+iprop
                    toStore.append({fullname:[ival]})
                #
                if inam == "New Material Definition":
                    fullname=pref_elem+"/"+"New Material Name"
                    toStore.append({fullname:[ival0]})
                #
                if inam == "New LAX Definition":
                    fullname=pref_elem+"/"+"New LAX Name"
                    toStore.append({fullname:[ival0]})
                #
                self.add_or_remove=1
                self.loadexception=True
                self.contextDB,update_void,ierr=self.updateDB(self.contextDB,self.pbType,toStore)
                self.loadexception=False
                if ierr==-1:
                    self.g4sfileError="error"
                    return
                #
        #
        #with open(self.g4sfile) as f:
        #    lines=f.readlines()
        #    self.contextDB = json.loads(lines[0])
        #    self.safirDB = json.loads(lines[1])

        #
#         ikey=[k for k in range(len(self.safirDB['children'])) if 'Problem Type' in self.safirDB['children'][k]["key"]][0]
#         self.pbType=self.safirDB['children'][ikey]["name"]
        #
        #Get the INfile name as global variable
        ikey=[k for k in range(len(self.safirDB['children'])) if 'Problem Type' in self.safirDB['children'][k]["key"]][0]
        tmp0=self.safirDB['children'][ikey]['props']
        ikey2=[k for k in range(len(tmp0)) if 'Name of the .IN File' in tmp0[k]["name"]][0]
        self.INfile=tmp0[ikey2]["values"][0]
        #
        # Get the number of VOIDS
        if(self.pbType=="Thermal 2D"):
            tmp0=self.getDBValue(self.contextDB,[("children","name","Curve"),("children","name","Thermal 2D"),("children","name","Void Constraint"),("children","name","-")],False)
            pgsents=[iprop for iprop in tmp0['props'] if not 'name' in list(iprop.keys())][0]
            self.nvoids=0
            for ityp in ['ents','pgs']:
                if(pgsents[ityp]!={}):
                    for k,v in pgsents[ityp].items():
                        val=[list(iv.values())[0] for iv in v if 'Void number' in list(iv.keys())][0][0]
                        self.nvoids=max(self.nvoids,val)

            #if(pgsents['pgs']!={}):
            print("self.nvoids Read: value=",self.nvoids)

        self.g4sfileError=""



    # Update the general lists: self.listMats and self.listLAX
    def updateGeneralLists(self):
        # Update list of Materials
        self.listMats=[]
        self.listLAX=[]
        #
        if('2D' in self.pbType):
            shpmax=2
        elif('3D' in self.pbType):
            shpmax=3
        #
        if('Structural' in self.pbType):
            listshps=[k+1 for k in range(shpmax)]
        else:
            listshps=[shpmax]

        print('listshps=',listshps)
        for i in listshps:
            tmp2=self.getDBValue(self.contextDB,[("children","name",self.allShapes[i]),("children","name",self.pbType),("children","name","New Material Definition")],False)
            rc=self.recursActionContextDB(tmp2,'list_names\tmat;'+str(i),self.listMats)
        #
        print("self.listMats=",self.listMats)
        #
        # Update list of LAX
        if('Structural 3D' in self.pbType):
            tmp2=self.getDBValue(self.contextDB,[("children","name","Curve"),("children","name",self.pbType),("children","name","New LAX Definition")],False)
            rc=self.recursActionContextDB(tmp2,'list_names\tlax;1',self.listLAX)
            print('init: self.listLAX=',self.listLAX)



    def idxInGeneralList(self,tmpl,inam,ishp): # Returns a table with index
        tmpidx=[k for k in range(len(tmpl)) if list(tmpl[k].keys())[0].split("/")[0]==inam+";"+str(self.allShapes.index(ishp))]
        return tmpidx


    # Create and Load the GUI menus in ONELAB.json from the ContextDB
    def loadContextDB(self,tmpg,pbtyp,do_add_from_pgsents):
        #
        # particular case of User-defined functions: if User-defined is chosen, then the 'File for..' additional prop is made visible=True
        # Remove from Thermal3D the Young module and Poisson coefficient
        for ishp in self.allShapes:
            if(self.pbType=="Thermal 3D" or (self.pbType=="Thermal 2D" and ishp!="Volume") or self.pbType=="Structural 3D" or (self.pbType=="Structural 2D" and ishp!="Volume")):
                tmp2=self.getDBValue(self.contextDB,[("children","name",ishp),("children","name",self.pbType)],False)
                rc=self.recursActionContextDB(tmp2,'filefor',"")

        # particular case of Rebar: will be treated as an image of "Curve Material" (no copy of "Curve Material", just a link to it)
        # Is "New Rebar Material Definition" the current selection?
        isRebarSelected=False
        if(self.pbType=="Structural 3D"):
            #
            # change flag stating that Rebar menu is selected, in order to switch the lst of materials from 2D to 1D
            tmp2=self.getDBValue(self.contextDB,[("children","name","Surface"),("children","name",self.pbType)],False)
            if(tmp2['children'][0]['name']=="New Rebar Material Definition"):
                isRebarSelected=True
            #
            # Change the visiblity conditionnally in contextDB, before loading to GUI menus
            tmp0=self.getDBValue(self.contextDB,[("children","name","Curve"),("children","name",self.pbType),("children","name","New LAX Definition"),("children","name","-")],False)['props']
            i1=[ k for k in range(len(tmp0)) if 'name' in tmp0[k] and "Check=LAX from" in tmp0[k]['name']][0]
            i2=[ k for k in range(len(tmp0)) if 'name' in tmp0[k] and "Rotation angle" in tmp0[k]['name']][0]
            i5=[ k for k in range(len(tmp0)) if 'name' in tmp0[k] and "Y'(dx,dy,dz)" in tmp0[k]['name'] ][0]
            #
            if(tmp0[i1]['values'][0]==1):
                tmp0[i2]['visible']=True
                tmp0[i5]['visible']=False
            else:
                tmp0[i2]['visible']=False
                tmp0[i5]['visible']=True
            #
        allmenus=[]
        for ishp in self.allShapes:
            prefixname='ONELAB Context'
            do_writeprf=True
            do_assignidx=False
            do_props_only=False
            lvl_max=999 #all levels of tree are exploredv
            menus=self.createContextMenu(self.contextDB,[ishp,pbtyp],lvl_max,prefixname,do_writeprf,do_assignidx,do_props_only,do_add_from_pgsents)
            #
            if(ishp=="Curve" and isRebarSelected):
                menuCurveMatDef=deepcopy(menus)
            allmenus+=menus
        allmenus=json.loads(json.dumps(allmenus))

        if(isRebarSelected):
            menus=[]
            for i in range(len(menuCurveMatDef)):
                imenu=menuCurveMatDef[i]
                if('Curve Template' in imenu['name'] and 'New Material Definition' in imenu['name']):
                    imenu['name']=imenu['name'].replace('Curve Template','Surface Template').replace('New Material Definition','New Rebar Material Definition')
                    imenu['name']=imenu['name'].replace('Material Names Choice','Rebar Material Names Choice')
                    menus.append(imenu)
            allmenus+=menus
        #Add the 'Update' and 'Remove' ONELAB Context buttons  in a 'Template' mode (ready for next instantiation by GMSH)
        for ishp in self.allShapes:
            if(self.pbType=="Thermal 3D" or (self.pbType=="Thermal 2D" and ishp!="Volume") or self.pbType=="Structural 3D" or (self.pbType=="Structural 2D" and ishp!="Volume")):
                prefix="ONELAB Context/"+ishp+" Template"
                # Add button
                menudict={}
                menudict["type"]="string"
                menudict["name"]=prefix+"/"+self.updateStr # prf_elem
                #print('menudict["name"]=',menudict["name"])
                menudict["values"]=["add "+prefix]
                menudict["attributes"]={"Macro":"Action", "Aspect":"RightReturnButton"}
                allmenus.append(menudict)
                #
                # Remove button
                menudict={}
                menudict["type"]="string"
                menudict["name"]=prefix+"/"+self.removeStr # prf_elem
                #print('menudict["name"]=',menudict["name"])
                menudict["values"]=["remove "+prefix]
                menudict["attributes"]={"Macro":"Action", "Aspect":"MiddleButton"}
                allmenus.append(menudict)

        # Add the Draw button for Local Axes
        if not self.isThermal:
            tmp0=self.getDBValue(self.contextDB,[("children","name","Curve"),("children","name",self.pbType)],False)['children']
            if(tmp0[0]['name']=="New LAX Definition"):
                prefix="ONELAB Context/Curve Template"
                # Draw axes button
                menudict={}
                menudict["type"]="string"
                menudict["name"]=prefix+"/"+self.drawStr # prf_elem
                #print('menudict["name"]=',menudict["name"])
                menudict["values"]=["draw "+prefix]
                menudict["attributes"]={"Macro":"Action", "Aspect":"MiddleButton"}
                allmenus.append(menudict)

            else:
                self.removeViewTag(self.LAXtag) # Remove local axes view when going to other menu than "Local Axes":
            #

        gmsh.onelab.set(json.dumps(allmenus))


    # Create and Load the GUI menus in ONELAB.json from the SafirDB
    def loadSafirDB(self):
        prefixname='0Modules/Solver/SAFIR/GENERAL'
        do_writeprf=False
        do_assignidx=True
        do_props_only=False
        lvl_max=999

        # Manage dependencies to hide/show some GUI menus
        if('Structural' in self.pbType):
            #
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType)],False)['props']
            i1=[ k for k in range(len(tmp0)) if tmp0[k]['name']=="Consider max displacement"][0]
            i2=[ k for k in range(len(tmp0)) if tmp0[k]['name']=="MAX DISPL" ][0]
            if(tmp0[i1]['values'][0]==1):
                tmp0[i2]['visible']=True
            else:
                tmp0[i2]['visible']=False
            #
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","key","outputs")],False)['props']
            i1=[ k for k in range(len(tmp0)) if "PRINTDEPL Print" in tmp0[k]['name']][0]
            i2=[ k for k in range(len(tmp0)) if "PRINTDEPL Tstart" in tmp0[k]['name'] ][0]
            if(tmp0[i1]['values'][0]==1):
                tmp0[i2]['visible']=True
            else:
                tmp0[i2]['visible']=False
            #
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","key","outputs")],False)['props']
            i1=[ k for k in range(len(tmp0)) if "PRINTFHE Print" in tmp0[k]['name']][0]
            i2=[ k for k in range(len(tmp0)) if "PRINTFHE Tstart" in tmp0[k]['name'] ][0]
            if(tmp0[i1]['values'][0]==1):
                tmp0[i2]['visible']=True
            else:
                tmp0[i2]['visible']=False
            #
        #
        if('Thermal 2D' in self.pbType):
            # Adjustments in visibility of menus, when special case of Torsion run
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","Run torsion analysis")],False)
            istorsrun=tmp0["values"]==[1]

            #tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","name","COMEBACK")],False)['props']
            #print("tmp0=",tmp0)
            #tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","key","Convergence"),("props","name","TIMESTEPMIN")],False)
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","key","Convergence")],False)
            iscomeback=False
            if(tmp0['name']=='COMEBACK'):
                iscomeback=True
            tmp0=tmp0['props']
            if(iscomeback):
                i1=[ k for k in range(len(tmp0)) if "TIMESTEPMIN" in tmp0[k]['name']][0]
                i2=[ k for k in range(len(tmp0)) if "TIMESTEP,UPTIME,TIMESTEPMAX" in tmp0[k]['name'] ][0]
                if istorsrun:
                    tmp0[i1]['visible']=False
                    tmp0[i2]['visible']=False
                else:
                    tmp0[i1]['visible']=True
                    tmp0[i2]['visible']=True
            else:
                i1=[ k for k in range(len(tmp0)) if "TIMESTEP,UPTIME(1)" in tmp0[k]['name']][0]
                i2=[ k for k in range(len(tmp0)) if "TIMESTEP,UPTIME(2)" in tmp0[k]['name'] ][0]
                if istorsrun:
                    tmp0[i1]['visible']=False
                    tmp0[i2]['visible']=False
                else:
                    tmp0[i1]['visible']=True
                    tmp0[i2]['visible']=True
            #
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","DIAG CAPA")],False)
            if istorsrun:
                tmp0['visible']=False
            else:
                tmp0['visible']=True
            #
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","TETA")],False)
            if istorsrun:
                tmp0['visible']=False
            else:
                tmp0['visible']=True
            #
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","TINITIAL")],False)
            if istorsrun:
                tmp0['visible']=False
            else:
                tmp0['visible']=True
            #
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","TIMEPRINT,UPTIMEPRINT")],False)
            if istorsrun:
                tmp0['visible']=False
            else:
                tmp0['visible']=True
            #
            # Special case of TSH run
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","key","TEM-TSH")],False)
            istsh=tmp0["name"]=="MAKE.TSH"
            #
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","Global center (Xo)")],False)
            tmp1=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","Global center (Yo)")],False)
            tmp2=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","Center of torsion (Xc)")],False)
            tmp3=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","Center of torsion (Yc)")],False)
            if istsh:
                tmp0['visible']=False
                tmp1['visible']=False
                tmp2['visible']=False
                tmp3['visible']=False
            else:
                tmp0['visible']=True
                tmp1['visible']=True
                tmp2['visible']=True
                tmp3['visible']=True

            #
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","key","Type of calculation")],False)
            print(tmp0["name"])
            if(tmp0["name"]!="USE_CURVES"):
                tmp0=tmp0['props']
                i1=[ k for k in range(len(tmp0)) if "Expected name " in tmp0[k]['name']][0]
                i2=[ k for k in range(len(tmp0)) if "IELEMTYPE" in tmp0[k]['name']][0]
                if istorsrun:
                    tmp0[i1]['visible']=False
                    tmp0[i2]['visible']=False
                else:
                    tmp0[i1]['visible']=True
                    tmp0[i2]['visible']=True
            #
        #
        basemenu=json.loads(baseparameters)
        # Run or not SAFIR exe
        menudict={}
        menudict["type"]="number"
        menudict["choices"]=[0, 1]
        menudict["name"]="0Modules/Solver/SAFIR/{}Also run SAFIR?"
        #print('menudict["name"]=',menudict["name"])

        # Get value
        tmp0=self.getDBValue(self.safirDB,[("props","name","Also run SAFIR?")],False)
        self.launchSAFIR=tmp0['values'][0]==1

        if(self.launchSAFIR and not 'SAFIREXE' in os.environ):
            msg="-- The environment variable SAFIREXE is not defined: cannot launch SAFIR"
            gmsh.logger.write(msg, level="error")
            self.launchSAFIR=False
        #Change status of 'ONELAB/Button'
        if(self.launchSAFIR):
            menudict["values"]=[1]
            idx=[i for i in range(len(basemenu)) if basemenu[i]['name']=="ONELAB/Button"][0]
            basemenu[idx]['values'][0]="Create .IN File and Launch SAFIR exe"
        else:
            menudict["values"]=[0]
            idx=[i for i in range(len(basemenu)) if basemenu[i]['name']=="ONELAB/Button"][0]
            basemenu[idx]['values'][0]="Create .IN File"

        #
        # Agregate basemenu and create menus from DB
        moremenus=self.createContextMenu(self.safirDB,[],lvl_max,prefixname,do_writeprf,do_assignidx,do_props_only,False)+basemenu
        moremenus.append(menudict)

        # Add infos
        menudict={}
        menudict["type"]="string"
        menudict["name"]="0Modules/Solver/SAFIR/0Version"
        menudict["values"]=[self.version]
        menudict["readOnly"]=True
        moremenus.append(menudict)
        menudict={}
        menudict["type"]="string"
        menudict["name"]="0Modules/Solver/SAFIR/1Authors"
        menudict["values"]=[self.authors]
        menudict["readOnly"]=True
        moremenus.append(menudict)

        #  Adjustments in visibility of menus, when special case of Torsion run

        if('Thermal 2D' in self.pbType):
            for i in range(len(moremenus)):
                menudict=moremenus[i]
                #
                if("Type of calculation" in menudict["name"]):
                    if istorsrun:
                        moremenus[i]['visible']=False
                    else:
                        moremenus[i]['visible']=True
                #
                if("Convergence" in menudict["name"]):
                    if istorsrun:
                        moremenus[i]['visible']=False
                    else:
                        moremenus[i]['visible']=True
                #
                if("TEM-TSH" in menudict["name"]):
                    if istorsrun:
                        moremenus[i]['visible']=False
                    else:
                        moremenus[i]['visible']=True


        gmsh.onelab.set(json.dumps(moremenus))
        gmsh.fltk.update()


    # Create and Load the GUI menus in ONELAB.json from the InspectDB
    def loadInspectDB(self,pbtyp):
        prefixname='0Modules/Solver/SAFIR/VIEW'
        do_writeprf=False
        do_assignidx=True
        do_props_only=True
        lvl_max=999
        moremenus=self.createContextMenu(self.inspectDB,[pbtyp],lvl_max,prefixname,do_writeprf,do_assignidx,do_props_only,False)

        # G4S Info button
        menudict={}
        menudict["type"]="string"
        menudict["name"]=prefixname+"/00Info on current props" # prf_elem
        #print('menudict["name"]=',menudict["name"])
        menudict["values"]=["viewg4s"]
        menudict["attributes"]={"Macro":"Action", "Aspect":"ReturnButton"}
        moremenus.append(menudict)

        # G4S Info button
        menudict={}
        menudict["type"]="string"
        menudict["name"]=prefixname+"/00Reload properties" # prf_elem
        #print('menudict["name"]=',menudict["name"])
        menudict["values"]=["reloadprops"]
        menudict["attributes"]={"Macro":"Action", "Aspect":"ReturnButton"}
        moremenus.append(menudict)

        gmsh.onelab.set(json.dumps(moremenus))
        gmsh.fltk.update()


    def drawLAX(self,act0):
        s=act0.split('/')
        #ishp=s[len(s)-2]
        ishp=s[len(s)-1]
        self.isViewLAX=True
        self.recreateLAXView(ishp)
        self.isViewLAX=False


    def recreateLAXView(self,ishp):
        #
        gmsh.option.setNumber('View.Axes',0) # Does not show the local axes
        gmsh.option.setNumber('View.ShowScale',0) # Show no color scale of the view

        pattern=re.compile("[0-9]+")
        itag=int(re.search(pattern, ishp).group(0))

        # if physgroup selected, select the first entity of this physgroup
        if("Physical" in ishp):
            ient=gmsh.model.getEntitiesForPhysicalGroup(1, itag)[0]
        else:
            ient=itag

        #Select the 2 points of the Curve
        shpedges=gmsh.model.getBoundary([(1, ient)],recursive=True)
        x=[];y=[];z=[]
        for ie in range(2):
            inode=abs(int(shpedges[ie][1]))
            tmp=gmsh.model.getValue(0, inode,[])
            x.append(tmp[0]);y.append(tmp[1]);z.append(tmp[2])
        #Get middle of the Curve
        x0=0.5*(x[0]+x[1]);y0=0.5*(y[0]+y[1]);z0=0.5*(z[0]+z[1])

        # First axis - scaled to Curve length
        VP=[]
        Xp=np.array([(x[1]-x[0]), (y[1]-y[0]), (z[1]-z[0])], dtype=np.float64)
        VP.append(Xp)
        normXp=LA.norm(Xp)
        Xp=Xp/normXp
        # Calculate matrix passing from X-axis to local Xp-axis
        X=np.array([1, 0, 0], dtype=np.float64)
        Y=np.array([0, 1, 0], dtype=np.float64)
        Z=np.array([0, 0, 1], dtype=np.float64)
        #
        # Perform additional rotation, from theta value
        #
        tmp0=self.getDBValue(self.contextDB,[("children","name","Curve"),("children","name",self.pbType),("children","name","New LAX Definition"),("children","name","-")],False)

        # theta value comes from new choice and change in first index of self.listLAX, due to permutation in menu 'LAX Names Choice'
        if self.permutespecial:
            lax_id=0
        # theta value comes from a loop on self.listLAX in manageInspect, to display all LAX
        elif self.LAXspecial:
            lax_id=self.laxid
        #
        if self.permutespecial or self.LAXspecial:
            checklax=[list(k.values())[0] for k in list(self.listLAX[lax_id].values())[0] if "Check=LAX from" in list(k.keys())[0]][0][0]
            reverse_xp=[list(k.values())[0] for k in list(self.listLAX[lax_id].values())[0] if "Reverse X" in list(k.keys())[0]][0][0]
            if(checklax==1):
                theta_degrees=[list(k.values())[0] for k in list(self.listLAX[lax_id].values())[0] if "Rotation angle" in list(k.keys())[0]][0][0]
            else:
                Yp_str=[list(k.values())[0] for k in list(self.listLAX[lax_id].values())[0] if "Y'(dx,dy,dz)" in list(k.keys())[0]][0][0].split(',')

            #
        #
        # theta values in other cases
        else:
            checklax=[iprop for iprop in tmp0['props'] if 'name' in iprop if "Check=LAX from" in iprop['name']][0]['values'][0]
            reverse_xp=[iprop for iprop in tmp0['props'] if 'name' in iprop and "Reverse X" in iprop['name']][0]['values'][0]
            if(checklax==1):
                theta_degrees=[iprop for iprop in tmp0['props'] if 'name' in iprop and "Rotation angle" in iprop['name']][0]['values'][0]
            else:
                Yp_str=[iprop for iprop in tmp0['props'] if 'name' in iprop and "Y'(dx,dy,dz)" in iprop['name']][0]['values'][0].split(',')
            #
        VP=[]
        if(reverse_xp==1):
            Xp=np.array([(x[0]-x[1]), (y[0]-y[1]), (z[0]-z[1])], dtype=np.float64)
            VP.append(Xp)
            normXp=LA.norm(Xp)
            Xp=Xp/normXp
        #
        if(checklax==1): #4th point determined by LAX with rotation angle
            print("theta_degrees=",theta_degrees)
            #
            if(theta_degrees!=0):
                theta=theta_degrees/180.*np.pi
                r0=np.array([[1,0,0],[0,np.cos(theta),-np.sin(theta)],[0,np.sin(theta),np.cos(theta)]])
                Y=np.dot(r0,Y)
                Z=np.dot(r0,Z)
            #
            v = np.cross(X,Xp)
            c = np.dot(X, Xp)
            s = LA.norm(v)
            if(s!=0):
                vx = np.array([[0, -v[2], v[1]], [v[2], 0, -v[0]], [-v[1], v[0], 0]])
                r = np.eye(3) + vx + np.dot(vx,vx)*(1-c)/(s**2)
            elif(c>=0):
                r=np.eye(3)
            else:
                r=np.array([[-1,0,0],[0,0,1],[0,1,0]]) # x'=-x,y'=z, z'=y
            #
            #Second axis and third axis - scaled to Curve length
            #Xp.append(np.dot(r,Y)*normXp);Xp.append(np.dot(r,Z)*normXp)
            Yp=np.dot(r,Y)
            Zp=np.dot(r,Z)
            VP.append(Yp);VP.append(Zp)
            #
        else:  #4th point determined by LAX with fix coordinates
            #
            VP=[]
            # A priori normalized Yp:
            Yp=np.array([float(Yp_str[0]), float(Yp_str[1]), float(Yp_str[2])], dtype=np.float64)
            if np.linalg.norm(Yp)==0:
                gmsh.logger.write("User-defined Y-Axis has zero coordinates!", level="error")
            if np.linalg.norm(np.cross(Xp,Yp))==0:
                gmsh.logger.write("Tangent Axis and user-defined Y-Axis cannot be colinear !", level="error")
                return(Yp[0],Yp[1],Yp[2])
            normYp=LA.norm(Yp)
            Yp=Yp/normYp
            Zp=np.cross(Xp,Yp)
            # new Yp
            Yp=np.cross(Zp,Xp)
            #
            VP.append(Xp);VP.append(Yp);VP.append(Zp)

        #
        # Re-create the list-based postpro view

        lstaxes=["x'","y'","z'"]
        floatfact=5.
        #
        if(self.ViewLAXOnce and self.isViewLAX):
            self.removeViewTag(self.LAXtag)
            t1 = gmsh.view.add("Beam Local Axes",self.LAXtag)
            self.pointLAX=[]
            self.nVPsLAX=0
        #
        if(self.isViewLAX):
            for i in range(3):
                self.pointLAX.extend([x0,y0,z0]) #point
                self.pointLAX.extend([VP[i][0]/floatfact, VP[i][1]/floatfact, VP[i][2]/floatfact]) # vectors
                gmsh.view.addListDataString(self.LAXtag, [x0+1.1*VP[i][0]/floatfact, y0+1.1*VP[i][1]/floatfact, z0+1.1*VP[i][2]/floatfact], [lstaxes[i]]) #point
                self.nVPsLAX+=1
        #
        if(self.ViewFinalLAX and self.isViewLAX):
            gmsh.view.addListData(self.LAXtag, "VP", self.nVPsLAX, self.pointLAX)
            gmsh.graphics.draw()
        #
        return(Yp[0],Yp[1],Yp[2])


    # Recreate thg GUI menus (ONELAB.json object) from the ContextDB, SafirDB and InspectDB
    def recreateContextMenusFromDB(self,ipb,do_add_from_pgsents):
        #
        gmsh.onelab.clear()
        #
        # Load now the updates from DBs to menus
#        print('listmat before=',self.listMats)
        self.updateGeneralLists()
#        print('listmat after=',self.listMats)
        self.loadContextDB(self.contextDB,ipb,do_add_from_pgsents)
        self.loadSafirDB()
        self.loadInspectDB(ipb)
        #
        s=deepcopy(json.loads(gmsh.onelab.get().replace("\\","/"))["onelab"]["parameters"])
        self.params= [k for k in s if 'SAFIR' in k['name'] or ipb in k['name']]
        #
        #print("safirDB on MAX DISPL=",[k for k in self.getDBValue(self.safirDB,[("children","name","Structural 2D")])['props'] if ('Consider max displacement' in k['name'] or 'MAX DISPL' in k['name'])])
        #print("GENERAL menus on MAX DISPL=",[k for k in s if 'GENERAL' in k['name'] and ('Consider max displacement' in k['name'] or 'MAX DISPL' in k['name'])])
        #print("all GENERAL menus=",[k for k in s if 'GENERAL' in k['name']])
        #
        gmsh.fltk.update()


    def getDBValue(self,tmpg,tabkeys,gotoCurrentLeaf):
        tmp0=tmpg
        for ikey in tabkeys:
            key1,key2,val=ikey
            idx=[i for i in range(len(tmp0[key1])) if(val in tmp0[key1][i][key2])][0]
            tmp0=tmp0[key1][idx]
        #
        if(gotoCurrentLeaf):
            found=False
            while(not found):
                if(tmp0["children"]==[]): # Select the leaves in the DB
                    found=True
                #
                else:
                    tmp0=tmp0['children'][0]
        #
        return tmp0


    # Converting the DBs (SafirDB and ContextDB) into GUI menus (ONELAB.json).
    # For ContextDB, first convert into Template, then update the menus with values from the entities/physgroups already stored in the ContextDB
    def createContextMenu(self,tmpg,list_vals,max_lvl,prf_categ,do_writeprf,do_assignidx,do_props_only,do_add_from_pgsents):
        # Go down to the n first levels, with selection of the branches having names in list_vals (n=len(list_vals))
        prf_elem0=prf_categ
        prf_elem=prf_categ
        prefix=[""]
        menus=[]
        end_lvl=0
        n_first_lvls=len(list_vals)
        tmp0=tmpg["children"]

        #
        i=0
        found=True
        while(i<n_first_lvls and found):
            itab=[idx for idx in range(len(tmp0)) if list_vals[i] in tmp0[idx]['name']]
            if(itab!=[]):
                idx=itab[0]
                inam=tmp0[idx]['name']
                ikey=tmp0[idx]['key']
                #
                if(not do_props_only):
                    tmp0=tmp0[idx]["children"]
                #
                if(do_writeprf):
                    if(prf_elem0=='ONELAB Context' and ikey=="Shape"):
                        prf_categ+='/'+ikey
                        prf_elem+='/'+inam+' Template'
                    else:
                        prf_categ+='/'+ikey
                        prf_elem+='/'+inam
                i+=1
            else:
                found=False
        #

        if(found):
            menus=[]
            if(not do_props_only):
                #Add Branches
                listRecurs=[{'key':prf_categ,'name':prf_elem,'data':[],'end_lvl':0}]

                listRecurs,menus=self.getLeaves(tmp0,prf_categ,prf_elem0,prf_elem,max_lvl,listRecurs,menus,do_writeprf) #recursively for SafirDB (ContextDB, with a single key per level, would not require recursion)

                print([(ilist['key'],ilist['name']) for ilist in listRecurs])

            else: # do_props_only
                for i in range(len(tmp0[idx]['props'])):
                    iprop=tmp0[idx]['props'][i]
                    menudict=deepcopy(iprop)
                    menudict['name']=prf_categ+"/"+iprop['name']
                    menus.append(menudict)
                return menus

            #Reassign the final indexes of menus
            if(do_assignidx):
                for  i in range(len(menus)):
                    imenu=menus[i]
                    s=imenu['name'].split('/')[-1]
                    r=imenu['name'].replace(s,'')
                    r+="%02d" % i+s
                    menus[i]['name']=r
            #
            # Special ONELAB Context : Generate the additional menus for the non-localized properties (Mats (therm and struct) and LAX (struct only)):

            if(prf_elem0=='ONELAB Context'):
                foundspecial=False
                for  i in range(len(menus)):
                    imenu=menus[i]
                    inam=imenu['name']
                    isnewmat=False;isnewlax=False
                    specialcase='New Material Definition' in inam or 'New LAX Definition' in inam or 'New Rebar Material Definition' in inam # Due to the creation of GUI menus, only of these two conditions can occur
                    #
                    if ('New Material Definition' in inam or 'New Rebar Material Definition' in inam) and self.listMats!=[]:
                        print('inam create=',inam,imenu)
                        isnewmat=True
                        tmplist=self.listMats
                        newname="Material Names Choice"
                    elif 'New LAX Definition' in inam and self.listLAX!=[]:
                        isnewlax=True
                        tmplist=self.listLAX
                        newname="LAX Names Choice"
                    #
                    if specialcase:
                        if(not foundspecial and (isnewmat or isnewlax)):
                            foundspecial=True #found the special case, perform following treatment only for one parameter of this property
                            #
                            s=inam.split("/")
                            pref=s[0]+"/"+s[1]+"/"+s[2]+"/"+s[3]
                            ishp=s[1].split(" ")[0]
                            idxshp=self.allShapes.index(ishp)
                            #
                            menudict={}
                            menudict['type']='number'
                            menudict['name']=pref+"/"+newname
                            menudict['values']=[0]
                            menudict['choices']=[]
                            menudict['valueLabels']={}
                            #
                            #print('tmplist=',tmplist)
                            foundshp=False # look for the elements in the list that have the same Shape as the current GUI menu
                            firstfoundshp=True # look for the first corresponding element in the list, to keep track of it
                            #
                            jsub=0
                            for j in range(len(tmplist)):
                                ival,_=list(tmplist[j].keys())[0].split("/")
                                #
                                ival,idim=ival.split(";")
                                if(int(idim)==idxshp): #Test if in the list
                                    menudict['valueLabels'][ival]=jsub
                                    menudict['choices'].append(jsub)
                                    jsub+=1
                                    foundshp=True
                                #
                                    if(firstfoundshp):
                                        chosename=ival
                                        firstfoundshp=False
                                #
                            #
                            if(foundshp): #if at least one
                                print('special menu:',menudict)
                                menus.append(menudict)
                            #
            #
            #
            # Special ONELAB Context : Change values in menus when properties are already stored in entities/physgroups in the DB
            if(prf_elem0=='ONELAB Context'):
                for ilist in listRecurs:
                    #
                    tmp1=ilist['data']
                    end_lvl=ilist['end_lvl']
                    print('end_lvl=',end_lvl) # DEBUG - print to evaluate the depth of the leaves
                    prf=ilist['name']
                    print('name=',prf) # DEBUG - print to evaluate the depth of the leaves
                    nprops=len(tmp1['props'])
                    #
                    # Specialcase: update from self.listMats or self.listLAX
                    if(self.permutespecial):
                        for i in range(len(menus)):
                            imenu=menus[i]
                            inam=imenu['name']
                            isnewmat=False;isnewlax=False
                            specialcase='New Material Definition' in inam or 'New LAX Definition' in inam or 'New Rebar Material Definition' in inam# Due to the creation of GUI menus, only of these two conditions can occur
                            #
                            if ('New Material Definition' in inam or 'New Rebar Material Definition' in inam) and self.listMats!=[]:
                                isnewmat=True
                                tmplist=self.listMats
                            elif 'New LAX Definition' in inam and self.listLAX!=[]:
                                isnewlax=True
                                tmplist=self.listLAX

                            if(isnewmat or isnewlax):
                                s=inam.split("/")
                                ishp=s[1].split(" ")[0]
                                tmpidx=self.idxInGeneralList(tmplist,chosename,ishp)
                                if(tmpidx!=[]):
                                    idx=tmpidx[0]
                                    for k in list(tmplist[idx].values())[0]:
                                        if(list(k.keys())[0] in inam):
                                            imenu['values']=list(k.values())[0]
                    #
                    #Add entities/physgroups present in Leafs
                    if(do_add_from_pgsents):
                        #
                        addmenus=[]
                        for iprop in tmp1['props']:
                            if not('name' in list(iprop.keys())):
                                for ikey in ['ents','pgs']:
                                    if(iprop[ikey]!={}):
                                        for inb in sorted(iprop[ikey]):
                                            for i in range(len(menus)):
                                                #
                                                imenu=menus[i]
                                                inam=imenu['name']
                                                specialcase='New Material Definition' in inam or 'New Rebar Material Definition' in inam or 'New LAX Definition' in inam
                                                #
                                                if(specialcase): # No update for specialcase, update has already been done
                                                    jnb,_=inb.split('/')
                                                    exclude_inb=True
                                                    #
                                                else:
                                                    jnb=inb
                                                    exclude_inb=False
                                                #
                                                if (not self.updateStr in inam) and (not self.removeStr in inam) and (not self.drawStr in inam) and (not 'HIDDEN' in inam) and (not exclude_inb): # Note: we don't recopy the buttons, they will be kept in a 'Template' mode
                                                    s=inam.split("/")
                                                    propnam=s[len(s)-1]
                                                    s0=s[1]
                                                    shptyp=s0.replace("Physical ","").split(" ")[0]
                                                    s1=shptyp+ " "+jnb
                                                    #print('inam=',inam)
                                                    if(ikey=="pgs"):
                                                        s1="Physical "+s1
                                                    jmenu=deepcopy(imenu)
                                                    jmenu['name']=inam.replace(s0,s1)
                                                    ""
                                                    if(len(s)-4==end_lvl):# This is a leaf of the tree
#                                                         print('propnam=',propnam)
#                                                         print('iprop[ikey][inb]=',iprop[ikey][inb])
                                                        jmenu['values']=[k for k in iprop[ikey][inb] if list(k.keys())[0]==propnam][0][propnam]
                                                        addmenus.append(jmenu)
                        #
                        menus+=addmenus
        #
        return menus


    #Called from "createContextMenu": generate recursively the list of DB children to be dressed
    def getLeaves(self,tmp0,prf_categ,prf_elem0,prf_elem,max_lvl,lists,menus,do_writeprf):
        end_lvl0=[ilist['end_lvl'] for ilist in lists if ilist['key']==prf_categ][0]

        if(tmp0!=[] and end_lvl0<max_lvl):

            #Generate the list of child sub-sets
            childsubsets={}
            for k in range(len(tmp0)):
                ikey=tmp0[k]['key']
                if(not ikey in childsubsets):
                    childsubsets[ikey]=[]
                childsubsets[ikey].append(k)

            lists=[ilist for ilist in lists if ilist['key']!=prf_categ] # is used to follow the branches in the recursive search in the tree
            for ik in childsubsets:
                # Evolve lists : Prepare next iteration of the set of menus
                ilist={}
                ilist['key']=prf_categ+'/'+ik
                ilist['name']=prf_elem
                #
#                 if(tmp0[childsubsets[ik][0]]["children"]!=[] or 1>0): # to put order in the ONELABContext window
#                     last0=ilist['name'].split('/')[-1]
#                     last1="00"+last0
#                     ilist['name']=ilist['name'].replace(last0,last1)
                #
                ilist['end_lvl']=end_lvl0+1
                ilist['data']=deepcopy(tmp0[childsubsets[ik][0]])

                lists.append(ilist)

                # Create the branching menus, can handle different sets of branches from one node
                tmpMenuDicts,ilist['name']=self.createBranchMenus(tmp0,ilist['name'],prf_elem0,childsubsets[ik],do_writeprf)
                menus+=tmpMenuDicts

                lists,menus=self.getLeaves(tmp0[childsubsets[ik][0]]["children"],ilist['key'],prf_elem0,ilist['name'],max_lvl,lists,menus,do_writeprf)
        return lists,menus


    #Called from "getLeaves": generate the GUI listboxes and textboxes
    def createBranchMenus(self, tmpg,prf,prf0,childsubset,do_writeprf):
        tmpmenus=[]
        # Generate the listboxes (from DB branch children list)
        menudict={}
        menudict['type']='number'
        menudict['values']=[0]
        menudict['choices']=[]
        menudict['valueLabels']={}

        ioffset=0
        for i in range(len(childsubset)):
            k=childsubset[i]
            if(i==0):
                s0=tmpg[k]['key']
                #s0="0"+s0 # to put order in the ONELABContext window
                s1=tmpg[k]['name']
                #
                #Special case for the PRINT and PRN in SAFIR Menu (struct):
                if(s0=="outputs" and s1=="PRINT"):
                    prf0+="/PRINT"
                #
                if(do_writeprf):
                    menudict['name']=prf+'/0'+s0
                    #menudict['name']=prf+"/"+s0
                    prf+='/'+s1
                else:
                    #menudict['name']=prf0+'/0'+s0
                    menudict['name']=prf0+'/'+s0
            #
            s1=tmpg[k]['name']
            if(s1!="-"):
                if("ONELAB Context" in prf and "Void SymAxis Constraint" in s1 and self.nvoids==0):
                    ioffset=1
                else:
                    menudict['valueLabels'][s1]=i-ioffset
                    menudict['choices'].append(i-ioffset)
        #
        if(menudict['choices']!=[]):
            tmpmenus.append(menudict)

        # Create the text boxes (from DB props on branches/leaves)
        i=0
        #
        k=childsubset[i]
        #
        if(tmpg[k]['props']!=[]):
            for ip in range(len(tmpg[k]['props'])):
                iprop=tmpg[k]['props'][ip]
                if 'name' in list(iprop.keys()) and not 'HIDDEN' in iprop['name']:
                    menudict=deepcopy(iprop)

                    # Special cases, conditioned by self;nvoids
                    if tmpg[k]["key"]=="Void Type" and iprop['name']=="Void number":
                        print('update max Void Type',self.nvoids+1)
                        iprop['values']=[1]
                        iprop['max']=self.nvoids+1
                    if tmpg[k]["key"]=="Void SymAxis Type" and iprop['name']=="Void number":
                        print('update max Void SymAxis Type',self.nvoids)
                        iprop['values']=[1]
                        iprop['max']=self.nvoids
                    #
                    if(do_writeprf):
                        menudict['name']=prf+"/"+iprop['name']
                    else:
                        menudict['name']=prf0+"/"+iprop['name']

                    tmpmenus.append(menudict)
        #
        return tmpmenus,prf


    def changeLabelToIdxOrNumerize(self,iprop,ivl):
        merror=""
        if(iprop['type']=="number"):
            if 'valueLabels' in iprop:
                if(not ivl[0] in iprop['choices']):
                    if ivl[0] in iprop['valueLabels']:
                        ivl=[iprop['valueLabels'][ivl[0]]]
                    else:
                        merror="Problem with "+str(ivl[0])+" not found in "+str(iprop['valueLabels'])
            #
            try:
                ivl=[int(str(ivl[0]))]
            except ValueError:
                ivl=[float(ivl[0])]
                #
            #
        return merror,ivl


    def permuteDB(self,tmp0,lists,prf_categ,found,endTree,shpid,inam,ivl,ivlstr,lvl,merror): # Recursive on all first elements when multi-elements at same level (ex. for the SAFIR general menu)
        #Notes: for safirDB, it permutes and change prop values - for contextDB, it only permutes

        permute=False
        end_lvl0=[ilist['end_lvl'] for ilist in lists if ilist['key']==prf_categ][0]

        if(not found and merror==""):
            #Generate the list of child sub-sets
            childsubsets={}
            for k in range(len(tmp0)):
                ikey=tmp0[k]['key']
                if(not ikey in childsubsets):
                    childsubsets[ikey]=[]
                childsubsets[ikey].append(k)

            lists=[ilist for ilist in lists if ilist['key']!=prf_categ]

            for ik in childsubsets:
                if(not found):
                    ilist={}
                    ilist['key']=prf_categ+'/'+ik
                    ilist['end_lvl']=end_lvl0+1
                    lists.append(ilist)

                    k0=childsubsets[ik][0]
                    tmpk0=tmp0[k0]
                    if(tmpk0['children']==[]):
                        endTree=True

                    #if(1>0):
                    if((lvl<999 and ilist['end_lvl']>=lvl) or(lvl==999)): # do explore only the correct level in the tree branches
                        #if("key" in tmpk0):
                        if(ivlstr!=""):
                                tabidx=[childsubsets[ik][idx] for idx in range(len(childsubsets[ik])) if tmp0[childsubsets[ik][idx]]['name']==ivlstr]
                                if(tabidx!=[]): #Permutation of menus
                                    found=True
                                    idx=tabidx[0]
                                    if(idx!=0):
                                        tmp0[idx],tmp0[k0]=tmp0[k0],tmp0[idx]
                                        permute=True
                                    #
                        #if(tmpk0['props']!=[] and not found): # Change value outside menus
                        if(tmpk0['props']!=[]):
                            tabidx=[idx for idx in range(len(tmpk0['props'])) if 'name' in tmpk0['props'][idx] if inam in tmpk0['props'][idx]['name']]
                            if(tabidx!=[]):
                                found=True
                                #
                                idx=tabidx[0]
                                #
                                if(ivl==-1):
                                    ivl=[tmpk0['props'][idx]['valueLabels'][ivlstr]]
                                else:
                                    iprop=tmpk0['props'][idx]
                                    merror,ivl=self.changeLabelToIdxOrNumerize(iprop,ivl)
                                    if(merror!=""):
                                        return tmp0,lists,permute,found,endTree,merror
                                        #

                                #
                                tmpk0['props'][idx]['values']=ivl

                                # Special case of 'Beam Local Axes' in ONELAB Context: launches recreateLAXView to adjust the vectors according to the value of theta
                                if(shpid!="-1" and ("Rotation angle" in inam or "Reverse X" in inam or "X'(dx,dy,dz)" in inam or "Y'(dx,dy,dz)" in inam or "Z'(dx,dy,dz)" in inam)):
                                    #
                                    # Verification in "New LAX Definition" concerning X',Y',Z':
                                    if "X'(dx,dy,dz)" in inam or "Y'(dx,dy,dz)" in inam or "Z'(dx,dy,dz)" in inam:
                                        ierr=self.isCorrectFormat(ivl[0],3,"Error in reading the fix coordinates - it shall be 3 floats separated by comma : ")
                                        if(ierr==-1):
                                            return tmp0,lists,permute,found,endTree
            #
                                    self.isViewLAX=True
                                    (xp0,yp0,zp0)=self.recreateLAXView(shpid)
                                    self.isViewLAX=False

                    if(not found and not endTree):
                        tmpk0["children"],lists,permute,found,endTree,merror=self.permuteDB(tmpk0["children"],lists,ilist['key'],found,endTree,shpid,inam,ivl,ivlstr,lvl,merror)

        return tmp0,lists,permute,found,endTree,merror


    def isCorrectFormat(self,ivl,nlen,emsg0):
        ierr=0
        try:
            tmpstr=ivl.split(",")
            if(len(tmpstr)!=nlen):
                raise ValueError("length shall be "+str(nlen))
        except ValueError as emsg:
            ierr=-1
            gmsh.logger.write(emsg0+str(emsg), level="error")
        return ierr


    #Changes in DB triggered from the 'Check' actions: perform permutations in the DB (in memory) from the GUI listbox modifications, and update values in the DB from the GUI textbox modifications
    # Note : no storage in the DB file for contextDB (triggered from 'Update/Remove' actions - see "updateDB"), but storage in the DB file for safirDB
    def manageContextMenus(self):
         #print "Enter check..."
         # Get new version of params after an event is caught by the API
         tmp0=gmsh.onelab.get()
         newparams=deepcopy(json.loads(tmp0.replace("\\","/")))["onelab"]["parameters"] # Solves the pb in Windows of conflict btw "\" and json.loads
         #
         otherSolverChanged=False
         pbtypChanged=False
         permute_safir=False
         ipb=self.pbType


         #Manage the changes triggered from the GUI modifications in the SAFIR General Menu
         for iparam in newparams:

            if(not iparam in self.params):
                if "Also run" in iparam['name']:
                    iprops=self.safirDB['props']
                    idx=[i for i in range(len(iprops)) if "Also run" in iprops[i]['name']][0]
                    self.safirDB['props'][idx]['values']=iparam['values']
                    otherSolverChanged=True
                #
                elif "SAFIR" in iparam['name']:
                    #
                    s=iparam['name'].split("/")[-1]
                    p=re.compile("^[0-9]+")
                    inam=p.sub('',s)
                    ivl=iparam["values"]
                    ivlbl={}
                    if("valueLabels" in iparam):
                        ivlbl=iparam["valueLabels"]
                    ivlstr=""
                    if(ivlbl!={}):
                        ivlstr=list(ivlbl.keys())[list(ivlbl.values()).index(ivl[0])]
                    #
                    found=False
                    endTree=False
                    merror=""
                    listRecurs=[{'key':"",'end_lvl':0}]
                    #self.safirDB['children'],listRecurs,permute_safir,found,endTree=self.permuteDB(self.safirDB['children'],listRecurs,found,endTree,inam,ivl,ivlstr,999) #Search not using indexation by levels, since no indexation in the name

                    self.safirDB['children'],listRecurs,permute_safir,found,endTree,merror=self.permuteDB(self.safirDB['children'],listRecurs,"",found,endTree,"-1",inam,ivl,ivlstr,999,merror)
                    #
                    if('Problem Type' in iparam['name']):
                        ipb=ivlstr
                        if(ipb!=self.pbType):
                            pbtypChanged=True
                            #
                            found=False
                            endTree=False
                            merror=""
                            listRecurs=[{'key':"",'end_lvl':0}]
                            self.contextDB['children'],listRecurs,permute,found,endTree,merror=self.permuteDB(self.contextDB['children'],listRecurs,"",found,endTree,"-1",inam,ivl,ivlstr,999,merror)
                            self.cleaningToClean()
                            gmsh.graphics.draw()
                            #
                    elif('Type of calculation' in iparam['name'] and 0>1): #Make 'Flux Constraint' in the ONELAB Context Panel dependent on the choice of 'USE_XXX' in SAFIR General Menu
                        # 2021-08-12: seems Obsolete, TBC by JMF
                         otherSolverChanged=True
                         #
                         levelChange=len("ONELAB Context/ / /Flux Constraint".split("/"))-3
                         nameChange="Flux Type"
                         newValChange=ivl
                         if('CURVES' in ivlstr):
                             newValChangeStr="User-defined"
                         else:
                             newValChangeStr="Pre-defined"
                         #                    shp0=inam.split('/')[1]
                         if(self.pbType=="Thermal 3D"):
                            shptypm="Surface"
                         else:
                            shptypm="Curve"
                         #

                         tmp0=self.getDBValue(self.contextDB,[("children","name",shptyp),("children","name",pbtyp)],False)['children']
#                          shpidx=[i for i in range(len(self.contextDB['children'])) if(shptypm in self.contextDB['children'][i]["name"])][0]
#                          tmp0=self.contextDB['children'][shpidx]['children']
#                          pbidx=[i for i in range(len(tmp0)) if(self.pbType in tmp0[i]["name"])][0]
#                          tmp0=tmp0[pbidx]["children"]
                         found=False
                         endTree=False
                         merror=""
                         listRecurs=[{'key':"",'end_lvl':0}]
                         tmp0,listRecurs,permute,found,endTree,merror=self.permuteDB(tmp0,listRecurs,"",found,endTree,"-1",nameChange,newValChange,newValChangeStr,levelChange,merror)
                         #
                         if(not 'CURVES' in ivlstr): # Adjust the '' in the ONELAB Context Panel according to the 'USE_XXX' in SAFIR General Menu
                             levelChange=len("ONELAB Context/ / /Flux Constraint/Flux Type".split("/"))-3
                             nameChange="Reserved"
                             _,newValChangeStr=ivlstr.split("_")
                             #
                             found=False
                             endTree=False
                             merror=""
                             listRecurs=[{'key':"",'end_lvl':0}]
                             tmp0,listRecurs,permute,found,endTree,merror=self.permuteDB(tmp0,listRecurs,"",found,endTree,"-1",nameChange,-1,newValChangeStr,levelChange,merror)
                         #
                    elif('Name of the .IN File' in iparam['name']):
                        self.INfile=ivl[0]
                        otherSolverChanged=True
                    else:
                        otherSolverChanged=True
         print("pbtypChanged=",pbtypChanged)
         print("otherSolverChanged=",otherSolverChanged)
         if(pbtypChanged or otherSolverChanged):
            print("Entered in 'pbtypChanged or otherSolverChanged'")
            if(self.pbType!=ipb):
                self.pbType=ipb
                self.isThermal="Thermal" in self.pbType

            self.recreateContextMenusFromDB(ipb,False)

             #Store safirDB after permutation
#             if os.path.exists(self.g4sfile):
#                 with open(self.g4sfile, 'r') as f:
#                     lines=f.readlines()
#                     ctxtDB = lines[0]
#                 with open(self.g4sfile, 'w') as f:
#                     f.write(ctxtDB)
#                     f.write(json.dumps(self.safirDB))
#             else:
#                 with open(self.g4sfile, 'w') as f:
#                     f.write(json.dumps(self.contextDB)+"\n")
#                     f.write(json.dumps(self.safirDB))
            self.viewAndWriteInfog4s(2)
            #
            return 0
         #

         # Manage the changes from GUI modifications in the "ONELAB Context" GUI Panel
         valChanged=False
         for iparam in newparams:
             if(not iparam in self.params):
                if "ONELAB Context" in iparam['name'] and (not self.updateStr in iparam['name']) and (not self.removeStr in iparam['name'] and (not self.drawStr in iparam['name'])):
                    #
                    inam=iparam['name']
                    s=inam.split("/")[-1]
                    p=re.compile("^[0-9]+")
                    inamshort=p.sub('',s)
                    ivl=iparam['values']
                    ivlbl={}
                    if("valueLabels" in iparam):
                        ivlbl=iparam["valueLabels"]
                    ivlstr=""
                    if(ivlbl!={}):
                        print('iparam=',iparam)
                        print('ivlbl=',ivlbl)
                        print('ivl[0]=',ivl[0])
                        ivlstr=list(ivlbl.keys())[list(ivlbl.values()).index(ivl[0])]
                    #
                    ioldparam=[ip for ip in self.params if ip['name']==inam]
                    shp0=inam.split('/')[1]
                    pattern=re.compile("[0-9]+")
                    #print ("shp0=",shp0)
                    inb=re.search(pattern, shp0).group(0)
                    shp1=shp0.replace(inb,'Template').replace("Physical ","")

                    inam1=inam.replace(shp0,shp1)

                    # Recall: btw 2 consecutive calls to gmsh.onelab.get (self.oldtmpparams and newtmpparams), only one parameter can change, that can only originate :
                    # (1) either from same entity/physgroup than before, then only 1 property change is detected,
                    # (2) or from a creation of entity/physgroup created from 'Template', then all properties of the new entity/physgroup are detected
                    #
                    # (Note: No values are changed only in the case where a different entity/physgroup has been selected -> valChanged keeps False)

                    if(ioldparam!=[]):
                        ipath="Existing" # same entity/phys group, param values are changed
                        # Store info on the change for potential permutation
                        valChanged=True
                        nameChange=inamshort
                        newValChange=ivl
                        newValChangeStr=ivlstr
                        nameLong=inam1
                        #levelChange=len(inam.split("/"))-3
                        levelChange=len(inam.split("/"))-4
                        shpType=shp1.split(" ")[0]
                        shpId=shp0

                    else:
                        #Store info on the change for potential permutation
                        ioldparam=[ip for ip in self.params if ip['name']==inam1]
                        # print('ioldparam=',ioldparam)
                        if(ioldparam[0]['values']!=ivl):
                            valChanged=True
                            nameChange=inamshort
                            ipath="Template"
                            newValChange=ivl
                            newValChangeStr=ivlstr
                            nameLong=inam1
                            #levelChange=len(inam.split("/"))-3
                            levelChange=len(inam.split("/"))-4
                            shpType=shp1.split(" ")[0]
                            shpId=shp0
                    # in this last if/else, only the change in entity/physgroup is not associated with valChangeed=True

         #Changes in the tDB file are not treated here for contextDB, but when Update/Remove buttons are clicked - Here only modifications in memory are treated (lost when software is closed)
         #
         print ("valChanged=",valChanged)
         if(valChanged):
             #
             permute=False
             #
             print('nameChange=',nameChange)
             print('newValChange=',newValChange)
             print('newValChangeStr=',newValChangeStr)
             #
             if(nameChange!='Material Names Choice' and nameChange!='LAX Names Choice' and nameChange!='Rebar Material Names Choice'):
                 tmp0=self.getDBValue(self.contextDB,[("children","name",shpType),("children","name",self.pbType)],False)['children']
                 #
                 found=False
                 endTree=False
                 merror=""
                 listRecurs=[{'key':"",'end_lvl':0}]
                 #
                 # particular case of Rebar: we trigger the permutation in "Curve Material" from the menu "New Rebar Material Definition"
                 if(newValChangeStr!="New Rebar Material Definition" and "New Rebar Material Definition" in nameLong):
                    shpId="-1"
                    tmp0=self.getDBValue(self.contextDB,[("children","name","Curve"),("children","name",self.pbType)],False)['children']
                   #
                 tmp0,listRecurs,permute,found,endTree,merror=self.permuteDB(tmp0,listRecurs,"",found,endTree,shpId,nameChange,newValChange,newValChangeStr,levelChange,merror)
                 self.permutespecial=False
             #
             else: # Special Case in ONELAB Context, for delocalized properties Mats and LAX
                 if(nameChange=='Material Names Choice'):
                     tmp0=self.getDBValue(self.contextDB,[("children","name",shpType),("children","name",self.pbType),("children","name","New Material Definition")],False)
                     tmplist=self.listMats
                     fieldname="New Material Name"
                 #
                 elif(nameChange=='Rebar Material Names Choice'):
                     shpType="Curve"
                     tmp0=self.getDBValue(self.contextDB,[("children","name",shpType),("children","name",self.pbType),("children","name","New Material Definition")],False)
                     tmplist=self.listMats
                     fieldname="New Material Name"
                 #
                 elif(nameChange=='LAX Names Choice'):
                     tmp0=self.getDBValue(self.contextDB,[("children","name",shpType),("children","name",self.pbType),("children","name","New LAX Definition")],False)
                     tmplist=self.listLAX
                     fieldname="New LAX Name"
                 #
                 tmp0=self.permuteDBspecial(tmp0,tmplist,nameChange,newValChange,newValChangeStr,fieldname,shpType,shpId)

                 permute=True
                 self.permutespecial=True
             #
             # particular case of Rebar: need permutation, in order to trigger modifications in "Curve Material" from the menu "New Rebar Material Definition"
             if(newValChangeStr=="New Rebar Material Definition"): # when changing to "New Rebar Material Definition", additionally permute the "Curve" to "New Material Definition"
                 tmp2=self.getDBValue(self.contextDB,[("children","name","Curve"),("children","name",self.pbType)],False)
                 i0=[i for i in range(len(tmp2['children'])) if tmp2['children'][i]['name']=="New Material Definition"][0]
                 tmp2['children'][i0],tmp2['children'][0]=tmp2['children'][0],tmp2['children'][i0]
             #
             print ("permute=",permute)
         #
         self.recreateContextMenusFromDB(self.pbType,False)
         return 0


    # Special Case permutation in ONELAB Context, for delocalized properties Mats and LAX
    def permuteDBspecial(self,tmp0,tmpl,inam,ivl,ivlstr,fdname,ishp,shpid):
        # Use recursion to find in ContextDB in which pg/ent the Mat or LAX is currently located
        paths=self.recursActionContextDB(tmp0,'find_path_to_name/'+fdname+'/'+ivlstr,None)
        ipath=[k for k in paths if 'True' in k][0]
        ipath.remove(ipath[0])
        ipath.remove(ipath[len(ipath)-1])
        ipath.append(ivlstr)
        #
        # Permute all properties in ContextDB
        rc=self.recursActionContextDB(tmp0,'permute_simple\t'+fdname,ipath)
        #
        # Permute in self.listMats or self.listLAX
        idx=self.idxInGeneralList(tmpl,ivlstr,ishp)[0]
        tmpl[idx],tmpl[0]=tmpl[0],tmpl[idx]

        if(fdname=="New LAX Name"):
            self.isViewLAX=True
            (xp0,yp0,zp0)=self.recreateLAXView(shpid)
            self.isViewLAX=False


    #Changes in DB triggered from the 'Update/Remove' actions: print to DB file
    def manageStoreDB(self,act0):
     #
        s=act0.split('/')
        #ishp=s[len(s)-2]
        ishp=s[len(s)-1]
        #
        shellmenus4verif=['Shell Material','Loads on Shell','Mass on Shell']
        #
        newparams=deepcopy(json.loads(gmsh.onelab.get().replace("\\","/"))["onelab"]["parameters"])
        do_change_void=True
        #
        #Need to determinate only the leaves among all the updates, the only elements that will be stored
        maxlvl=-999
        for iparam in newparams:
                if ishp in iparam['name'] and (not self.updateStr in iparam['name']) and (not self.removeStr in iparam['name']):
                    maxlvl=max(maxlvl,len(iparam['name'].split('/')))
        #
        toStore=[]
        #
        # Gather all parameters of the property to be changed in the DB on file
        #
        for iparam in newparams:
            #Verification of SAME Constraint
            if("Point" in ishp and not "Physical" in ishp and 'SAME Constraint' in iparam['name']):
                #print("PROBLEM - iparam in manageStoreDB=",iparam)
                gmsh.logger.write("SAME Constraint cannot be attributed to single point !", level="error")
                return -1
            # Verification for proper form in Correspondance table (is performed at this stage, for future use in listProps)
            if "New Material Name" in iparam['name']:
                try:
                    lst0=iparam['values'][0].split('-')
                except Exception as emsg:
                    gmsh.logger.write("Problem in the syntax of Material Name:"+str(emsg), level="error")
                    return -1
            elif('Surface' in ishp and [icateg for icateg in shellmenus4verif if icateg in iparam['name']]!=[]):
                emsg=self.verifShellGeom(ishp)
                if emsg!="":
                    gmsh.logger.write("Error in Shell Geometry: "+str(err), level="error")
                    return -1
            #
            if ishp in iparam['name'] and (not self.updateStr in iparam['name']) and (not self.removeStr in iparam['name']):
                inam=iparam['name']
                s=iparam['name'].split('/')
                ilvl=len(s)
                #
                isShellRebar=False #Verification of empty field is not done here, but in UpdateDB
                if('Shell Rebar' in inam and "Angle(s)" in inam):
                    isShellRebar=True
                if('Shell Rebar' in inam and "Normal-X(s)" in inam):
                    isShellRebar=True
                if('Shell Rebar' in inam and "Normal-Y(s)" in inam):
                    isShellRebar=True
                if('Shell Rebar' in inam and "Normal-Z(s)" in inam):
                    isShellRebar=True
                #
                if(ilvl==maxlvl):
                    ivl=iparam['values']
                    #Update contextDB
                    propnam=s[len(s)-1]
                    if((ivl==[''] or ivl=='') and not isShellRebar and not 'File for' in propnam):
                        gmsh.logger.write("Parameter "+propnam+" has no value. Please provide one", level="error")
                        ierr=-1
                        return ierr
                    toStore.append({inam:ivl})
        #
        self.contextDB,update_void,ierr=self.updateDB(self.contextDB,self.pbType,toStore)
        #
        #print("all_previous_found=",all_previous_found)
                    #print ("iparam=",iparam)
        if(ierr==0):
            if(update_void or self.add_or_remove==1 or self.add_or_remove==0):
                self.recreateContextMenusFromDB(self.pbType,True)
            #
#             if os.path.exists(self.g4sfile):
#                 with open(self.g4sfile, 'r') as f:
#                     lines=f.readlines()
#                     sfDB = lines[1]
#                 with open(self.g4sfile, 'w') as f:
#                     f.write(json.dumps(self.contextDB)+"\n")
#                     f.write(sfDB.replace("\n",""))
#             else:
#                 with open(self.g4sfile, 'w') as f:
#                     f.write(json.dumps(self.contextDB)+"\n")
#                     f.write(json.dumps(self.safirDB))
            self.viewAndWriteInfog4s(2)
            #
            return 0
        else:
            return ierr


    def verifShellGeom(self,ishp):
        emsg=""
        if('Physical' in ishp):
            itag=int(ishp.replace("Physical Surface ",""))
            ients=gmsh.model.getEntitiesForPhysicalGroup(1, itag)
        else:
            itag=int(ishp.replace("Surface ",""))
            ients=[itag]
        #
        for ient in ients:
            #
            # First, verify for each individual entity, that it has 4 corners
            shpedges=gmsh.model.getBoundary([(2, int(ient))],recursive=True)
            if(len(shpedges)!=4):
                    return "Entity 'Surface "+str(ient)+"' should have 4 corners when defined as a Shell"
            #
            # Secondly, verify that the polygon is convex
            triplets=[(0,1,2),(1,2,3),(2,3,0),(3,0,1)]
            #for itriplet in triplets:
        return emsg


    #Called by manageStoreDB and by GetG4SJson
    def updateDB(self,tmpg,pbtyp,toStore):
        #
        ierr=0
        #
        def getParam(i):
            inam=list(toStore[i].keys())[0]
            ivl=list(toStore[i].values())[0]
            s=inam.split('/')
            s0=copy(s)
            s=s[len(s)-1]
            propnam=s
            return inam,propnam,ivl
        #
        inam,propnam,ivl=getParam(0)
        
        p=re.compile("^[0-9]+")
        toStoreNames=[re.sub(p,"",getParam(i)[1]) for i in range(len(toStore))]
        
        s=inam.split('/')

        #
        s0=copy(s)
        isVoidConstraint="Void Constraint" in s0
        #
        print('inam=',inam)
        iprop=s[3]
        #
        shp0=inam.split('/')[1]
        pattern=re.compile("[0-9]+")
        inb=str(re.search(pattern, shp0).group(0))
        #
        if "Physical" in shp0:
            ityp="Physical"
        else:
            ityp="Entity"
        shptyp=shp0.replace("Physical ","").split(" ")[0]
        #
        def recurs_cleaning(tmpg,prev,ityp,shptyp,inb,inewfield,imatlax,specialcase):
             #newidx=0
             if(tmpg["children"]==[]):  # Select the leaves in the DB
                 if not prev:
                     ik=[k for k in range(len(tmpg["props"])) if not 'name' in tmpg["props"][k]][0]
                     #
                     if(ityp=='Physical'):
                         ikey='pgs'
                         #itypname='Physical '+shptyp+' '+inb
                     else:
                         ikey='ents'
                         #itypname=shptyp+' '+inb

                     tmp1=tmpg["props"][ik][ikey]
                     tmp1keys=list(tmp1.keys())
                     #
                     if(tmp1keys!=[]): # if ent/pysgroup exists for this property
                         #
                         if(not specialcase): # normal case: find the ent/physgroup "inb" in a similar property (mat or lax) and remove it
                             if(inb in tmp1keys):
                                 prev=True
                         #
                         else: #specialcase: find the "inam" in parameter"inewfield" of a similar property (mat or lax) and remove it (can be stored for any "inb")
                             ifound=False
                             for tmp1key in tmp1keys: # loop on ent/physgroup
                                 if not ifound:
                                     for iprop in tmp1[tmp1key]:
                                         inam=list(iprop.keys())[0]
                                         if(inewfield in inam):
                                             ivl=list(iprop.values())[0][0]
                                             if(ivl==imatlax):
                                                 prev=True
                                                 inb=tmp1key
                         #
                         if(prev):
                             del tmp1[inb]
             #
             else:
                for newidx in range(len(tmpg["children"])):
                    prev,tmpg["children"][newidx]=recurs_cleaning(tmpg["children"][newidx],prev,ityp,shptyp,inb,inewfield,imatlax,specialcase)
             return prev,tmpg
        #

        # Added a specialcase is defined for Mats and LAX: the only properties that are unlocalized properties
        specialcase='New Material Definition' in inam or 'New LAX Definition' in inam  or 'New Rebar Material Definition' in inam
        print('specialcase=',specialcase)
        previous_found=False;update_void=False
        isnewmat=False;isnewlax=False;ismatidx=False;islaxidx=False

        # specialcase: Verifications:
        if(specialcase):
            #
            # particular case of Rebar: trigger modifications in "Curve Material" from the menu "New Rebar Material Definition"
            if 'New Rebar Material Definition' in inam:
                shptyp="Curve"
                iprop="New Material Definition"
            #
            if 'New Material Definition' in inam  or 'New Rebar Material Definition' in inam:
                isnewmat=True
                inewfield='New Material Name'
                imatlax=[list(isto.values())[0] for isto in toStore if(inewfield in list(isto.keys())[0])][0][0]
                ismatidx=self.idxInGeneralList(self.listMats,imatlax,shptyp)!=[]

            #
            elif 'New LAX Definition' in inam:
                isnewlax=True
                inewfield='New LAX Name'
                imatlax=[list(isto.values())[0] for isto in toStore if(inewfield in list(isto.keys())[0])][0][0]
                islaxidx=self.idxInGeneralList(self.listLAX,imatlax,shptyp)!=[]

            #Verification of no spaces in name of new material:
            for i in range(len(toStore)):
                inam,propnam,ivl=getParam(i)
                if(inewfield in inam):
                    iverif=len(ivl[0].strip().split())>1
                    if(iverif):
                        gmsh.logger.write(inewfield+" cannot contain spaces: put underscores if needed in your name", level="error")
                        ierr=-1
                        return tmpg,update_void,ierr
            #
            # Verification in "New LAX Definition" concerning X',Y',Z':
            for i in range(len(toStore)):
                inam,propnam,ivl=getParam(i)
                if('New LAX Definition' in inam and "X'(dx,dy,dz)" in inam or "Y'(dx,dy,dz)" in inam or "Z'(dx,dy,dz)" in inam):

                    ierr=self.isCorrectFormat(ivl[0],3,"Error in reading the fix coordinates - it shall be 3 floats separated by comma : ")
                    if(ierr==-1):
                        return tmpg,update_void,ierr

            #
            if(self.add_or_remove==1 and imatlax=="" and isnewmat):
                gmsh.logger.write("Material to add shall have a name. Please provide one", level="error")
                ierr=-1
                return tmpg,update_void,ierr
            if(self.add_or_remove==1 and imatlax=="" and isnewlax):
                gmsh.logger.write("LAX to add shall have a name. Please provide one", level="error")
                ierr=-1
                return tmpg,update_void,ierr
            #
            if(self.add_or_remove==0):
                if(isnewmat and not ismatidx):
                    gmsh.logger.write("Weird: this name is not found in Material list. Please provide an existing Material to remove", level="error")
                    ierr=-1
                    return tmpg,update_void,ierr
                if(isnewlax and not islaxidx):
                    gmsh.logger.write("Weird: this name is not found in LAX list. Please provide an existing LAX to remove", level="error")
                    ierr=-1
                    return tmpg,update_void,ierr
            #
            # Separate 2cases: Add and Update
            if(self.add_or_remove==1 and isnewmat and ismatidx):
                self.add_or_remove=2 # Update instead of Add
            if(self.add_or_remove==1 and isnewlax and islaxidx):
                self.add_or_remove=2 # Update instead of Add

        #
        # not specialcase: verifications:
        else:
            if(self.add_or_remove==1):
                self.add_or_remove=2

                #Verification in "Shell Rebar" concerning the Angle and/or Normal-X,Normal-Y, Normal-Z:
                isShellRebar=False
                for i in range(len(toStore)):
                    inam,propnam,ivl=getParam(i)
                    if('Shell Rebar' in inam and "Angle(s)" in inam):
                        isShellRebar=True
                        angles=ivl[0].strip().split()
                    if('Shell Rebar' in inam and "Normal-X(s)" in inam):
                        normX=ivl[0].strip().split()
                    if('Shell Rebar' in inam and "Normal-Y(s)" in inam):
                        normY=ivl[0].strip().split()
                    if('Shell Rebar' in inam and "Normal-Z(s)" in inam):
                        normZ=ivl[0].strip().split()


                if isShellRebar:
                    ierr,emsg,nelembars=self.angleShellRebar(angles,normX,normY,normZ,0)
                    #
                    if ierr!=0:
                        gmsh.logger.write("Error in Shell Rebar: "+emsg, level="error")
                        ierr=-1
                        return tmpg,update_void,ierr

                    # Verify also with the other fields the coherence
                    otherRebarFields=['Material Name(s)','Section(s)','Level(s)']
                    for i in range(len(toStore)):
                        inam,propnam,ivl=getParam(i)
                        for irebar in otherRebarFields:
                            if('Shell Rebar' in inam and irebar in inam):
                                isShellRebar=True
                                ivalue=ivl[0].strip().split()
                                #
                                if(irebar!='Material Name(s)'):
                                    for iv in ivalue:
                                        try:
                                            iconv=float(iv)
                                        except ValueError as emsg:
                                            ierr=-1
                                            gmsh.logger.write("Error in reading "+irebar+" : "+str(emsg), level="error")
                                            return tmpg,update_void,ierr
                                #
                                if(len(ivalue)!=nelembars):
                                    ierr=-1
                                    gmsh.logger.write("Error in reading '"+irebar+"': not same number of elements as in Angle(s) or in Normal-X(s), Normal-Y(s), Normal-Z(s) !", level="error")
                                    return tmpg,update_void,ierr

                # Verification in "Oblique Support" concerning X',Y',Z':
                for i in range(len(toStore)):
                    inam,propnam,ivl=getParam(i)
                    if('Oblique Support' in inam and "Point2(x,y)" in inam or "Point2(x,y,z)" in inam or "Point3(x,y,z)" in inam):
                        if("Point2(x,y)" in inam):
                            ierr=self.isCorrectFormat(ivl[0],2,"Error in reading the fix coordinates - it shall be 2 floats separated by comma : ")
                            if(ierr==-1):
                                return tmpg,update_void,ierr
                        if("Point2(x,y,z)" in inam or "Point3(x,y,z)" in inam):
                            ierr=self.isCorrectFormat(ivl[0],3,"Error in reading the fix coordinates - it shall be 3 floats separated by comma : ")
                            if(ierr==-1):
                                return tmpg,update_void,ierr
                #
                #Verify that the Material Names allocated to objects are in the list
                #
                tmpk=[k for k in self.specialCategs if k[0] in inam]

                if(tmpk!=[]):
                    #
                    for i in range(len(tmpk)):
                        imatlax=tmpk[i][1]
                        idim=tmpk[i][2]
                        imeth=tmpk[i][3]
                        #
                        if(imatlax=='mats'):
                            tmpl=self.listMats
                            inewfield='Material Name(s)'
                        else:
                            tmpl=self.listLAX
                            inewfield='LAX Name'
                        #
                        ivaltab=[list(isto.values())[0] for isto in toStore if(inewfield in list(isto.keys())[0])][0][0]
                        #
                        if(imeth=='one'):
                            ival=ivaltab
                            # Verify that only one element has been entered (not separated by spaces
                            iconv=ival.strip().split()
                            if(len(iconv)>1):
                                ierr=-1
                                gmsh.logger.write("Error in reading "+inewfield+" - either different elements entered, though only one is required - or entered some spaces in the name", level="error")
                                return tmpg,update_void,ierr
                            #
                            tmpidx=self.idxInGeneralList(tmpl,ival,self.allShapes[idim])
                            if(tmpidx==[]):
                                gmsh.logger.write(inewfield+" "+ival+" is not in the current list. Please define it first before allocating", level="error")
                                ierr=-1
                                return tmpg,update_void,ierr
                        else:
                            ivaltab=ivaltab.strip().split() #split the list of mats or lax, split on spaces - ex. '   nam1   nam3 nam5    ' split as ['nam1', 'nam3', 'nam5']
                            for ival in ivaltab:
                                tmpidx=self.idxInGeneralList(tmpl,ival,self.allShapes[idim])
                                if(tmpidx==[] and not self.loadexception):
                                    gmsh.logger.write(inewfield+" "+ival+" is not in the current list. Please define it first before allocating", level="error")
                                    ierr=-1
                                    return tmpg,update_void,ierr
        #
        # Treat first the removing part for Remove and for Update (for this latter: we remove the version in the previous ent/pg and reload it in the current ent/pg)
        if(self.add_or_remove==0 or self.add_or_remove==2):
            #
            tmp0=self.getDBValue(tmpg,[("children","name",shptyp),("children","name",pbtyp),("children","name",iprop)],False)

            if not specialcase: # Try to find the ent/pg "inb" in the same ityp of the similar properties
                previous_found,tmp0=recurs_cleaning(tmp0,previous_found,ityp,shptyp,inb,"","",specialcase)
            #
            else: # Try to find the inewfield=imatlax (name of mat or lax) first in ents then in pgs on the similar properties
                previous_found,tmp0=recurs_cleaning(tmp0,previous_found,"Entity",shptyp,inb,inewfield,imatlax,specialcase)
                if not previous_found:
                    previous_found,tmp0=recurs_cleaning(tmp0,previous_found,"Physical",shptyp,inb,inewfield,imatlax,specialcase)
            #

        #
        if isVoidConstraint:
            update_void=previous_found
        #
        if(self.add_or_remove>=1):

            # Find the location of the property in the DB, go to the current leaf
            tmp0=self.getDBValue(tmpg,[("children","name",shptyp),("children","name",pbtyp),("children","name",iprop)],True)

            ik=[k for k in tmp0["props"] if not 'name' in k][0]
            p=re.compile("^[0-9]+")
            tmp2=[re.sub(p,"",k['name']) for k in tmp0["props"] if 'name' in k]
            #
            if(ityp=='Physical'):
                ikey='pgs'
            else:
                ikey='ents'
            tmp1=ik[ikey]
            #
            # Finds in tmp1 if the current (ent/pg, property) already has an entry defined in the DB
            if specialcase:
                p=re.compile("^"+inb+"/")
                tmp1keys=[k for k in list(tmp1.keys()) if(re.search(p,k)!=None)]
                icond=tmp1keys==[]
                if tmp1keys!=[]:
                   imax=max([int(k.split("/")[1]) for k in tmp1keys]) # number of occurences of a same material
            else:
                icond=not inb in list(tmp1.keys())
            #
            
            if(icond): # the current (ent/pg, property) has no entry defined in the DB
                if specialcase:
                    tmp1key=inb+"/0"
                else:
                    tmp1key=inb
                #
                tmp1[tmp1key]=[]
                for i in range(len(toStore)):
                    inam,propnam,ivl=getParam(i)
                    iprop=[k for k in tmp0["props"] if 'name' in k and propnam in k['name']][0]
#                     print('iprop=',iprop)
#                     print('ivl=',ivl)
                    merror,ivl=self.changeLabelToIdxOrNumerize(iprop,ivl)
                    if(merror!=""):
                        gmsh.logger.write(merror, level="error")
                        ierr=-1
                        return tmpg,update_void,ierr
                    nearpropnam=[k['name'] for k in tmp0["props"] if 'name' in k and propnam in k['name']][0]
                    tmp1[tmp1key].append({nearpropnam:ivl})
                #
                print("toStoreNames=",toStoreNames)
                #Complete with props not in toStore (because visible=False)
                for i in range(len(tmp2)):  
                    print('tmp2[i]=',tmp2[i])
                    if(not tmp2[i] in toStoreNames):
                        ikmiss=[k for k in tmp0["props"] if 'name' in k and tmp2[i] in k['name']][0]
                        #print('ikmiss=',ikmiss)
                        nearpropnam=[k['name'] for k in tmp0["props"] if 'name' in k and tmp2[i] in k['name']][0]
                        #print('nearpropnam=',nearpropnam)
                        tmp1[tmp1key].append({nearpropnam:ikmiss['values']})
            #
            else: # the current (ent/pg, property) has already entry(ies) defined in the DB - can only be the case for specialcase (for no specialcase, this property has been removed)
                tmp1key=inb+"/"+str(imax+1)
                tmp1[tmp1key]=[]
                
                for i in range(len(toStore)):
                    inam,propnam,ivl=getParam(i)
                    iprop=[k for k in tmp0["props"] if 'name' in k and propnam in k['name']][0]
                    merror,ivl=self.changeLabelToIdxOrNumerize(iprop,ivl)
                    if(merror!=""):
                        gmsh.logger.write(merror, level="error")
                        ierr=-1
                        return tmpg,update_void,ierr
                    nearpropnam=[k['name'] for k in tmp0["props"] if 'name' in k and propnam in k['name']][0]
                    tmp1[tmp1key].append({nearpropnam:ivl})
                    #
                #
                #Complete with props not in toStore (because visible=False)
                for i in range(len(tmp2)):   
                    if(not tmp2[i] in toStoreNames):
                        ikmiss=[k for k in tmp0["props"] if 'name' in k and tmp2[i] in k['name']][0]
                        nearpropnam=[k['name'] for k in tmp0["props"] if 'name' in k and tmp2[i] in k['name']][0]
                        tmp1[tmp1key].append({nearpropnam:ikmiss['values']})
            #print("tmp1[tmp1key]=",tmp1[tmp1key])
        #
        #Special adjustment for VoidConstraint: increase number of voids
        if isVoidConstraint and self.add_or_remove==0 and update_void: # for Remove: update the nvoids
            self.nvoids-=1
        if isVoidConstraint and self.add_or_remove>=1:
            self.nvoids+=1

        # Do an update on the general Lists
        if(specialcase):
            self.updateGeneralLists()
            self.permutespecial=True

        return tmpg,update_void,ierr


    # Used by UpdateDB to verify the coherence of the angles inputs (iflag==0), and used by listprops to constitute either (1) the list (iflag==1) or (2) the string for display (iflag==2)
    def angleShellRebar(self,angles,normX,normY,normZ,iflag):
        ierr=0
        strAngles=""
        nelems=0
        if(iflag==0):
            #
            if(angles==[] and (normX==[] or normY==[] or normZ==[])):
                ierr=-1
                strAngles="If angles is Empty, normX,normY and normZ shall not be Empty - or reverse"
                return ierr,strAngles,nelems
            #
            elif(angles!=[] and (normX==[] or normY==[] or normZ==[])): # The angle decription is supposed to be found only in "angles"
                #
                for iangle in angles:
                    try:
                        iconv=float(iangle)
                    except ValueError as emsg:
                        ierr=-1
                        return ierr,"Error in reading Angle(s) : "+str(emsg),nelems
                nelems=len(angles)
            #
            elif(angles==[] and normX!=[] and normY!=[] and normZ!=[]): # The angle decription is supposed to be found only in "normX,normy,normZ"
                #
                norms=[(normX,"Normal-X(s)"),(normY,"Normal-Y(s)"),(normZ,"Normal-Z(s)")]
                #
                for inorm in norms:
                    for ix in inorm[0]:
                        try:
                            iconv=float(ix)
                        except ValueError as emsg:
                            ierr=-1
                            return ierr,"Error in reading "+inorm[1]+" : "+str(emsg),nelems
                #
                lennorms=[]
                for inorm in norms:
                    lennorms.append(len(inorm[0]))
                if(len(list(set(lennorms)))>1):
                    ierr=-1
                    return ierr,"Error in reading 'Normal(s): not same number of elements in Normal-X(s), Normal-Y(s), Normal-Z(s) !",nelems
                nelems=len(norms[0][0])
            #
            else: # The angle decription is supposed to be a combination of elements in "angles" and in "normX,normy,normZ"
                for iangle in angles:
                    try:
                        if iangle.upper()!="N/A":
                            iconv=float(iangle)
                    except ValueError as emsg:
                        ierr=-1
                        return ierr,"Error in reading Angle(s) : "+str(emsg),nelems
                nelems=len(angles)
                #
                norms=[(normX,"Normal-X(s)"),(normY,"Normal-Y(s)"),(normZ,"Normal-Z(s)")]
                #
                for inorm in norms:
                    for ix in inorm[0]:
                        try:
                            if ix.upper()!="N/A":
                                iconv=float(ix)
                        except ValueError as emsg:
                            ierr=-1
                            return ierr,"Error in reading "+inorm[1]+" : "+str(emsg),nelems
                #
                lennorms=[]
                for inorm in norms:
                    lennorms.append(len(inorm[0]))
                if(len(list(set(lennorms)))>1):
                    ierr=-1
                    return ierr,"Error in reading 'Normal(s): not same number of elements in Normal-X(s), Normal-Y(s), Normal-Z(s) !",nelems
                nelems2=len(norms[0][0])
                #
                if(nelems!=nelems2):
                    ierr=-1
                    return ierr,"Error in reading 'Normal(s): not same number of elements in Angle(s) and in Normal-X(s), Normal-Y(s), Normal-Z(s) !",nelems
                #
                for i in range(nelems):
                    if(angles[i].upper()=='N/A' and (normX[i].upper()=="N/A" or normY[i].upper()=="N/A" or normX[i].upper()=="N/A" )):
                        ierr=-1
                        return ierr,"Error in reading 'Normal(s): too many N/As between Angle(s) and Normal-X(s), Normal-Y(s), Normal-Z(s) !",nelems
                    elif(angles[i].upper()!='N/A' and normX[i].upper()!="N/A" and normY[i].upper()!="N/A" and normX[i].upper()!="N/A"):
                        ierr=-1
                        return ierr,"Error in reading 'Normal(s): too few N/As between Angle(s) and Normal-X(s), Normal-Y(s), Normal-Z(s): cannot infer which treatment is the good one !",nelems
        #
        else: # iflag==1
            angs={};norms={}
            if(angles!=[] and [iangle for iangle in angles if iangle.upper()=="N/A"]==[]): # Angles are fully described in "angles"
                strAngles="angles=("
                for i in range(len(angles)):
                    iangle=angles[i]
                    angs[i]=float(iangle)
            #
            elif(angles==[]): # Angles are fully described in "normX,..."
                strAngles="normals=("
                for i in range(len(normX)):
                    nx=normX[i];ny=normY[i];nz=normZ[i]
                    norms[i]=[float(nx),float(ny),float(nz)]
            #
            else: # Angles are described in both
                for i in range(len(angles)):
                    iangle=angles[i]
                    if(iangle.upper()!="N/A"):
                        angs[i]=float(iangle)
                    else:
                        nx=normX[i];ny=normY[i];nz=normZ[i]
                        norms[i]=[float(nx),float(ny),float(nz)]
            #
            if(iflag==2):
                if(angs!={}):
                    strAngles="angles=("
                    first=True
                    for i,iangle in angs.items():
                        if first:
                            strAngles+=str(iangle)
                            first=False
                        else:
                            strAngles+=","+str(iangle)
                    strAngles+=")"
                if(norms!={}):
                    if(strAngles==""):
                        strAngles="norms=("
                    else:
                        strAngles+=" - norms=("
                    #
                    first=True
                    for i,inorm in norms.items():
                        if first:
                            strAngles+="("+str(inorm[0])+","+str(inorm[1])+","+str(inorm[2])+")"
                            first=False
                        else:
                            strAngles+=",("+str(inorm[0])+","+str(inorm[1])+","+str(inorm[2])+")"
                    strAngles+=")"

            #
            if(iflag==1):

                strAngles=angs.copy()
                strAngles.update(norms)
            #
            nelems=len(angs)+len(norms)

        return ierr,strAngles,nelems


    #Write a string in Fortran format -  2021-12-15 Change this function into a free format txt file (no more Fortran formatted)
    def writeLineFortran(self,fmtstr,vallist):
        #fmt = ff.FortranRecordWriter(fmtstr)
        #return fmt.write(vallist)
        for i in range(len(vallist)):
            ival=vallist[i]
            if i==0:
                str0=str(ival)
            else:
                str0+=" "+str(ival)
        return str0


    #Store the nodes and faces in coherent order for SAFIR
    def getOrderedFaces(self,ielemtype,ielemnodes):
        facenodes=[]
        if(ielemtype==1): # lines
            facenodes.append(ielemnodes)
        if(ielemtype==2): #triangles
            facenodes.append([ielemnodes[0],ielemnodes[1]])
            facenodes.append([ielemnodes[1],ielemnodes[2]])
            facenodes.append([ielemnodes[2],ielemnodes[0]])
        if(ielemtype==3): #quadrangles
            facenodes.append([ielemnodes[0],ielemnodes[1]])
            facenodes.append([ielemnodes[1],ielemnodes[2]])
            facenodes.append([ielemnodes[2],ielemnodes[3]])
            facenodes.append([ielemnodes[3],ielemnodes[0]])
        if(ielemtype==4): #tets
            facenodes.append([ielemnodes[0],ielemnodes[1],ielemnodes[2]])
            facenodes.append([ielemnodes[0],ielemnodes[3],ielemnodes[2]])
            facenodes.append([ielemnodes[0],ielemnodes[1],ielemnodes[3]])
            facenodes.append([ielemnodes[1],ielemnodes[2],ielemnodes[3]])
        if(ielemtype==5): #hexas
            facenodes.append([ielemnodes[0],ielemnodes[3],ielemnodes[7],ielemnodes[4]])
            facenodes.append([ielemnodes[2],ielemnodes[3],ielemnodes[7],ielemnodes[6]])
            facenodes.append([ielemnodes[1],ielemnodes[2],ielemnodes[6],ielemnodes[5]])
            facenodes.append([ielemnodes[0],ielemnodes[1],ielemnodes[5],ielemnodes[4]])
            facenodes.append([ielemnodes[0],ielemnodes[1],ielemnodes[2],ielemnodes[3]])
            facenodes.append([ielemnodes[4],ielemnodes[5],ielemnodes[6],ielemnodes[7]])
        if(ielemtype==6): #prisms
            facenodes.append([ielemnodes[0],ielemnodes[2],ielemnodes[5],ielemnodes[3]])
            facenodes.append([ielemnodes[1],ielemnodes[2],ielemnodes[5],ielemnodes[4]])
            facenodes.append([ielemnodes[0],ielemnodes[1],ielemnodes[4],ielemnodes[3]])
            facenodes.append([ielemnodes[0],ielemnodes[1],ielemnodes[2]])
            facenodes.append([ielemnodes[3],ielemnodes[4],ielemnodes[5]])
        return facenodes



    def listProps(self,ndims,do_regroup):
        # Routine to recursively collect the information (material, flux,...) of the entities and physical groups, keeping track of the variations in properties (adding final index)
        # Note: includes also default properties to recall the 'choices' and 'valueLabels' when needed
        PropAtts={};PropPgs={};PropEnts={};PropValPgs={};PropValEnts={};PropExtValPgs={};PropExtValEnts={};propstrs=[];uniqmatlist=[]
        shptyp="";shptypm="";nmats=0

        if(ndims==3):
            ishptyp=3
            ishptypm=2
        else:
            ishptyp=2
            ishptypm=1
        shptyp=self.allShapes[ishptyp]
        shptypm=self.allShapes[ishptypm]


        def get_objs_from_json(tmpg,istr,lf,ityp): #by recursion
            istr0=istr
            for idict in tmpg:
                if(idict['children']==[]):
                    if(istr==""):
                        istr=idict['name']
                    else:
                        istr=istr0+"/"+idict['name']
                    i=[k for k in range(len(idict["props"])) if not 'name' in idict["props"][k]][0]
                    tmp1=idict['props'][i][ityp]
                    pps=[idict["props"][k] for k in range(len(idict["props"])) if 'name' in idict["props"][k]]
                    if(tmp1!={}):
                        for k,v in tmp1.items():
                            if([ik for ik in lf if istr in ik]==[]):
                                idx="0"
                                jstr=istr+"/"+idx
                                lf[jstr]={"props":v,ityp:[k],"defaultprops":pps}
#                                 if('torsname' in idict and ndims==2):
#                                     lf[jstr]['torsname']=idict['torsname']
                            else:
                                p=re.compile("[0-9]+$")
                                found=False
                                maxidx=0
                                for ik in list(lf.keys()):
                                    if istr in ik:
                                        inb=re.search(p, ik).group(0)
                                        maxidx=max(maxidx,int(inb))
                                        if(v==lf[ik]["props"]):
                                            if(not ityp in lf[ik]):
                                                lf[ik][ityp]=[]
                                            lf[ik][ityp].append(k)
                                            found=True
                                if not found:
                                    jnb=maxidx+1
                                    jk=istr+"/"+str(jnb)
                                    lf[jk]={"props":v,ityp:[k],"defaultprops":pps}
                else:
                    if(istr==""):
                        jstr=idict['name']
                    else:
                        jstr=istr+"/"+idict['name']
                    get_objs_from_json(idict['children'],jstr,lf,ityp)


        # Define the property attributes from contextDB, with entities and groups, different for Thermal and Structural
        if(self.isThermal):
            #propstrs=[('mats;'+str(ishptyp),'Material'),('flxs;'+str(ishptypm),'Flux Constraint'),('frtiers;'+str(ishptypm),'Frontier Constraint')] # (name of property in tables;dimension , name of property in contextDB)

            propstrs=[('flxs;'+str(ishptypm),'Flux Constraint'),('frtiers;'+str(ishptypm),'Frontier Constraint')]
            propstrs.append(('mats;'+str(ishptyp),self.allShapes[ishptyp]+' Material'))
            propstrs.append(('blks;0','Block Constraint'))
            propstrs.append(('blks;1','Block Constraint'))
            propstrs.append(('same;0','SAME Constraint'))
            propstrs.append(('same;1','SAME Constraint'))
            propstrs.append(('same;2','SAME Constraint'))
            if(ndims==3):
                propstrs.append(('blks;2','Block Constraint'))
                propstrs.append(('same;3','SAME Constraint'))
            if(ndims==2):
                propstrs.append(('void;1','Void Constraint'))
                if(self.nvoids>0):
                    propstrs.append(('void_sym;1','Void SymAxis Constraint'))
                propstrs.append(('real_sym;1','Real SymAxis Constraint'))
                propstrs.append(('tors;0','Torsion Point Constraint'))
        else: # Structural
            propstrs.append(('blks;0','Block Constraint'))
            propstrs.append(('blks;1','Block Constraint'))
            propstrs.append(('obliqdispl;0','Oblique Support for displ'))
            propstrs.append(('obliqrot;0','Oblique Support for rot'))
            propstrs.append(('same;0','SAME Constraint'))
            propstrs.append(('same;1','SAME Constraint'))
            propstrs.append(('same;2','SAME Constraint'))
#
            #
            if(ndims==3):
                propstrs.append(('beamlax;1','Beam Section Local Axes'))
                propstrs.append(('solcormat;3','Solid Material'))
                propstrs.append(('shcormat;2','Shell Material'))
                propstrs.append(('sload;2','Loads on Shell'))
                propstrs.append(('mass;2','Mass on Shell'))
                propstrs.append(('rebar;2','Shell Rebar'))
#                 propstrs.append(('same;3','SAME Constraint'))
            #
            propstrs.append(('beamcormat;1','Beam Section Type'))
            propstrs.append(('trusscormat;1','Truss Section Type'))
            propstrs.append(('spring;0','Spring'))
            propstrs.append(('beamrelax;1','Relaxation Beam'))
            propstrs.append(('sload;0','Loads on Node'))
            propstrs.append(('sload;1','Unif Distr Loads on Beam'))
            propstrs.append(('tgload;1','Beam Trapezoidal Global Loads'))
            propstrs.append(('tlload;1','Beam Trapezoidal Local Loads'))
            propstrs.append(('hydrostat;1','Beam Hydrostatic Loads'))
            propstrs.append(('mass;0','Mass on Node'))
            propstrs.append(('mass;1','Mass on Beam'))


        print('propstrs=',propstrs)

        for iprop in propstrs:
            try:
                igtypdim=iprop[0]
                igtyp,idim=igtypdim.split(';')
                idim=int(idim)
                ishp=self.allShapes[idim]
                igname=iprop[1]
                # Collect entity and physical group
                #
                tmp0=self.getDBValue(self.contextDB,[("children","name",ishp),("children","name",self.pbType),("children","name",igname)],False)['children']
                PropAtts[igtypdim]={}
                get_objs_from_json(tmp0,"",PropAtts[igtypdim],'ents')
                get_objs_from_json(tmp0,"",PropAtts[igtypdim],'pgs')
            except Exception as emsg:
                gmsh.logger.write("Problem in collecting "+igtypdim+" property attributes:"+str(emsg), level="error")
                return -1,PropAtts,PropPgs,PropEnts,PropValPgs,PropValEnts,PropExtValEnts,PropExtValPgs,propstrs,ishptyp,ishptypm,nmats,uniqmatlist

        #TDB - add here a verification of coherence btw geo model and g4sDB


        # Thermal Only: Add a unique void indexing
        if(self.isThermal):
            try:
                    if(ndims==2):
                        for i, (k, v) in enumerate(PropAtts['void;1'].items()):
                            ikey=PropAtts['void;1'][k]
                            ivoid=[list(iv.values())[0] for iv in ikey['props'] if 'Void number' in list(iv.keys())][0][0]
                            ikey["val"]=ivoid
                            ikey["extend_val"]=str(ivoid)+'- void Boundary'
                        #
                        if(self.nvoids>0):
                            for i, (k, v) in enumerate(PropAtts['void_sym;1'].items()):
                                ikey=PropAtts['void_sym;1'][k]
                                ivoid=[list(iv.values())[0] for iv in ikey['props'] if 'Void number' in list(iv.keys())][0][0]
                                ikey["val"]=i+1
                                ikey["extend_val"]=str(ivoid)+'- void symAxis'
                        #
                        for i, (k, v) in enumerate(PropAtts['real_sym;1'].items()):
                            ikey=PropAtts['real_sym;1'][k]
                            ikey["val"]=i+1
                            ikey["extend_val"]=i+1
                #
            except Exception as emsg:
                gmsh.logger.write("Problem in void property attributes:"+str(emsg), level="error")
                return -1,PropAtts,PropPgs,PropEnts,PropValPgs,PropValEnts,PropExtValEnts,PropExtValPgs,propstrs,ishptyp,ishptypm,nmats,uniqmatlist

        tmp0=self.getDBValue(self.contextDB,[("children","name","Surface"),("children","name","Thermal 2D"),("children","name","New Material Definition"),\
                                            ("children","name","Insulations"),("children","name","Insulation")],False)
        print("tmp0=",tmp0)
        print('PropAtts=',PropAtts)
        print('listMats=',self.listMats)

        # Separate physgroups and entities
        #
        for iprop in propstrs:
            igtypdim=iprop[0]
            igtyp,idim=igtypdim.split(';')
            try:
                #
                PropPgs[igtypdim]=[];PropEnts[igtypdim]=[];PropValPgs[igtypdim]=[];PropValEnts[igtypdim]=[];PropExtValPgs[igtypdim]=[];PropExtValEnts[igtypdim]=[]
                #
                for k,v in PropAtts[igtypdim].items():
                    #
                    if igtyp =='beamcormat':
                        valtab=[[val0 for k0,val0 in d.items()] for d in v["props"]]
                        #
                        extval=valtab[0][0][0]+" - "+valtab[1][0][0]
                        #
                        val=extval
                    #
                    elif igtyp =='beamlax':
                        valtab=[[val0 for k0,val0 in d.items()] for d in v["props"]]
                        #
                        extval=str(valtab[0][0][0])
                        #
                        val=extval
                    #
                    elif igtyp =='trusscormat':
                        valtab=[[val0 for k0,val0 in d.items()] for d in v["props"]]
                        #
                        extval=str(valtab[0][0][0])+" - "+str(valtab[1][0][0])+" - "+str(valtab[2][0][0])+" - "+str(valtab[3][0][0])
                        #
                        val=extval
                    #
                    elif igtyp =='solcormat':
                        valtab=[[val0 for k0,val0 in d.items()] for d in v["props"]]

                        if(self.SolidFilename!="" and str(valtab[0][0][0])!=self.SolidFilename):
                            gmsh.logger.write("Problem in Solid Material allocation: .OUT filename has already been assigned a different value (only one value possible): "+self.SoldFilename, level="error")
                            return -1,PropAtts,PropPgs,PropEnts,PropValPgs,PropValEnts,PropExtValEnts,PropExtValPgs,propstrs,ishptyp,ishptypm,nmats,uniqmatlist
                        #
                        self.SolidFilename=str(valtab[0][0][0])
                        #
                        #
                        extval=str(valtab[0][0][0])+" - "+str(valtab[1][0][0])+" - "+str(valtab[2][0][0])+" - "+str(valtab[3][0][0])+" - "+str(valtab[4][0][0])
                        #
                        val=extval
                    #
                    elif igtyp =='shcormat':
                        valtab=[[val0 for k0,val0 in d.items()] for d in v["props"]]
                        #
                        extval=str(valtab[0][0][0])+" - "+str(valtab[1][0][0])+" - "+str(valtab[2][0][0])+" - "+str(valtab[3][0][0])
                        #
                        val=extval
                    #
                    elif igtyp=='mass':
                        valtab=[[val0 for k0,val0 in d.items()] for d in v["props"]]
                        #
                        nvals=len(valtab)
                        for ival in range(nvals):
                            if(ival==0):
                                extval=str(valtab[0][0][0])
                            else:
                                extval+=" - "+str(valtab[ival][0][0])
                        #
                        val=extval
                    #
                    elif 'load' in igtyp or 'hydrostat' in igtyp:
                        #
                        # Treat first Load Function with its labels, and potential 'File For'
                        for i0 in range(len(v["props"])):
                            iprop=v["props"][i0]
                            propnam=list(iprop.keys())[0]
                            j0=[j for j in range(len(v["defaultprops"])) if v["defaultprops"][j]['name']==propnam][0]
                            idefprop=v["defaultprops"][j0]
                            #
                            for k0,val0 in iprop.items():
                                if('Load Function' in k0 and not 'File for' in k0):
                                    lbls=idefprop['valueLabels']
                                    extval=[i for i,w in lbls.items() if w==val0[0]][0]
                                    if(extval=="User-defined"):
                                        extval=[v1 for jprop in v["props"] for k1,v1 in jprop.items()  if 'File for Load Function' in k1][0][0]
                        # Treat other parameters
                        for i0 in range(len(v["props"])):
                            iprop=v["props"][i0]
                            for k0,val0 in iprop.items():
                                if (not 'Load Function' in k0):
                                    extval+=' - '+str(val0[0])
                        #
                        val=extval
                    #
                    elif igtyp =='beamrelax':
                        valtab=[[val0 for k0,val0 in d.items()] for d in v["props"]]
                        #
                        if("3D" in self.pbType):
                            ndofelem=14
                        else:
                            ndofelem=6
                        #
                        for i in range(ndofelem):
                            if(i==0):
                                extval=str(valtab[1][0][0])
                            else:
                                extval+=" - "+str(valtab[i][0][0])
                        #
                        val=extval
                    #
                    elif 'obliq' in igtyp:
                        valtab=[[val0 for k0,val0 in d.items()] for d in v["props"]]
                        #
                        if("3D" in self.pbType):
                            extval=str(valtab[0][0][0])+" - "+str(valtab[1][0][0])
                        else:
                            extval=str(valtab[0][0][0])
                        #
                        val=extval
                    #
#                     elif igtyp =='hydrostat':
#                         valtab=[[val0 for k0,val0 in d.items()] for d in v["props"]]
#                         #
#                         extval=str(valtab[0][0][0])+" - "+str(valtab[1][0][0])
#                         #
#                         val=extval
                    #
                    elif igtyp =='mats':
                        valtab=[[val0 for k0,val0 in d.items()] for d in v["props"]]
                        extval=valtab[0][0][0]
                        # Get number
                        val=str([k0 for k0 in range(len(self.listMats)) if extval+";"+idim in list(self.listMats[k0].keys())[0]][0]+1)
                    #
                    elif igtyp == 'rebar':
                        for d in v["props"]:
                            key=list(d.keys())[0]
                            val1=list(d.values())[0][0]
                            if("Material Name(s)" in key):
                                matrebar=val1
                            if("Section(s)" in key):
                                sectrebar=val1
                            if("Level(s)" in key):
                                levrebar=val1
                            if("Angle(s)" in key):
                                angles=val1.strip().split()
                            if("Normal-X(s)" in key):
                                normX=val1.strip().split()
                            if("Normal-Y(s)" in key):
                                normY=val1.strip().split()
                            if("Normal-Z(s)" in key):
                                normZ=val1.strip().split()
                        # il manque thickness, shell mat
                        ierr,emsg,nelembars=self.angleShellRebar(angles,normX,normY,normZ,1)
                        extval="rebars="+str(len(matrebar.strip().split()))+": mats='"+matrebar+"'"
                        val=str(nelembars)+"/"+matrebar+"/"+sectrebar+"/"+levrebar+"/"+str(emsg)
                    #
                    elif igtyp == 'same':
                        extval=""
                        #valtab=[[val0 for k0,val0 in d.items()] for d in v["props"]]
                        for d in v["props"]:
                            key=list(d.keys())[0]
                            val1=list(d.values())[0][0]
                            for d0 in v["defaultprops"]:
                                for k0,val0 in d0.items():
                                    if val0==key:
                                        lbltab=d0["valueLabels"]
                            s0=[k0 for k0,val0 in lbltab.items() if val0==val1][0]
                            if(extval==""):
                                extval=s0
                            else:
                                extval+=" - "+s0
                        #
                        val=extval
                    #
                    elif not 'void' in igtyp and igtyp !='real_sym': #blks, flux, frtiers

                        # All params are valueLabels
                        ifirst=True
                        for i0 in range(len(v["props"])):
                            iprop=v["props"][i0]
                            propnam=list(iprop.keys())[0]
                            j0=[j for j in range(len(v["defaultprops"])) if v["defaultprops"][j]['name']==propnam][0]
                            idefprop=v["defaultprops"][j0]
                            #                                                     #
                            for k0,val0 in iprop.items():
                                if(not 'File for' in k0):
                                    print(k0)
                                    lbls=idefprop['valueLabels']
                                    print(lbls)
                                    extval0=[i for i,w in lbls.items() if w==val0[0]][0]
                                    if(extval0=="User-defined"):
                                        pattern=re.compile("^[0-9]+")
                                        str0=re.search(pattern,propnam).group(0)
                                        propnam=propnam.replace(str0,'')
                                        extval0=[v1 for jprop in v["props"] for k1,v1 in jprop.items()  if 'File for '+propnam in k1][0][0]
                                    if ifirst:
                                        extval=extval0
                                        ifirst=False
                                    else:
                                        extval+=" - "+extval0

                        val=extval
                    #
                    elif 'void' in igtyp or igtyp =='real_sym':
                        val=v['val']
                        extval=str(v['extend_val'])
                    #
                    else:
                        print('coucou_fin:',igtyp)
                        val="1"
                        extval="1"

                    #
                    if 'pgs' in list(v.keys()):
                        PropPgs[igtypdim]+=v['pgs']
                        PropValPgs[igtypdim]+=[val for i in range(len(v['pgs']))]
                        PropExtValPgs[igtypdim]+=[extval for i in range(len(v['pgs']))]
                    #
                    if 'ents' in list(v.keys()):
                        PropEnts[igtypdim]+=v['ents']
                        PropValEnts[igtypdim]+=[val for i in range(len(v['ents']))]
                        PropExtValEnts[igtypdim]+=[extval for i in range(len(v['ents']))]
                    #
            except Exception as emsg:
                gmsh.logger.write("Problem in separation of entities and physgroups in the '"+igtypdim+"' property attributes:"+str(emsg), level="error")
                return -1,PropAtts,PropPgs,PropEnts,PropValPgs,PropValEnts,PropExtValEnts,PropExtValPgs,propstrs,ishptyp,ishptypm,nmats,uniqmatlist

            try:
                # Verifications - [ TBD - Indicate precisely where exactly the double definitions occurs ]
                #
                if(len(list(set(PropPgs[igtypdim])))!=len(PropPgs[igtypdim])):
                #if(len(list(set(PropPgs[igtypdim])))!=len(PropPgs[igtypdim]) and not (self.isThermal==False and 'mats' in igtypdim)): # Verify that 1 group did not receive 2 different props (except for Global Material of Structural)
                    raise ValueError("Pb - Each physical group can only have at maximum one "+igtypdim+" definition")
                #
                if(len(list(set(PropEnts[igtypdim])))!=len(PropEnts[igtypdim])):
                #if(len(list(set(PropEnts[igtypdim])))!=len(PropEnts[igtypdim]) and not (self.isThermal==False and 'mats' in igtypdim)): # Verify that 1 entity did not receive 2 different props (except for Global Material of Structural)
                    raise ValueError("Pb - Each entity can only have at maximum one "+igtypdim+" definition")
                #
            except Exception as emsg:
                gmsh.logger.write("Problem in the verification of entities and physgroups in the "+igtypdim+" property attributes:"+str(emsg), level="error")
                return -1,PropAtts,PropPgs,PropEnts,PropValPgs,PropValEnts,PropExtValEnts,PropExtValPgs,propstrs,ishptyp,ishptypm,nmats,uniqmatlist


        if(do_regroup): #For Inspect only

            # Transform PropPgs en PropEnts
            for iprop in propstrs:
                igtypdim=iprop[0]
                igtyp,idim=igtypdim.split(';')
                idim=int(idim)
                if not (igtyp=='mats' and self.isThermal==False): # Structural: as a specialcase, 'Structural Global Material' is kept only in the PropAtts table, not in the subsequent tables
                    if(PropPgs[igtypdim]!=[]):
                        for i in range(len(PropPgs[igtypdim])):
                            ipgs=PropPgs[igtypdim][i]
                            ipgsval=PropExtValPgs[igtypdim][i]
                            for ient in gmsh.model.getEntitiesForPhysicalGroup(idim, int(ipgs)):
                                PropEnts[igtypdim].append(str(ient))
                                PropExtValEnts[igtypdim].append(str(ipgsval))


        print("PropExtValEnts=",PropExtValEnts)
        print("PropEnts=",PropEnts)

        print("PropExtValPgs=",PropExtValPgs)
        print("PropPgs=",PropPgs)
        # Note: propstrs is exported only for "do_regroup" in "manageInspect"

        return 0,PropAtts,PropPgs,PropEnts,PropValPgs,PropValEnts,PropExtValEnts,PropExtValPgs,propstrs,ishptyp,ishptypm,nmats,uniqmatlist


    # Extract from internal SafirDB in two different modes: (1) iflag=1: for display as info in the GUI, (2) and iflag=2: for writing the .g4s file (new version)
    #
    def prepWriteGenProps(self,llog,iflag):
        if('Thermal 2D' in self.pbType):
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","Run torsion analysis")],False)
            istorsrun=tmp0["values"]==[1]
        else:
            istorsrun=False
        #
        tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType)],False)['props']
        for k in range(len(tmp0)):
            if('valueLabels' in tmp0[k]):
                ival=[k0 for k0,v0 in tmp0[k]['valueLabels'].items() if v0==tmp0[k]['values'][0]][0]
                llog.append(str(tmp0[k]['name'])+" : "+str(ival))
            else:
                llog.append(str(tmp0[k]['name'])+" : "+str(tmp0[k]['values'][0]))

        tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType)],False)['children']
        childsubsets={}
        for k in range(len(tmp0)):
            ikey=tmp0[k]['key']
            if(not ikey in childsubsets):
                childsubsets[ikey]=[]
            childsubsets[ikey].append(k)

        for ik in childsubsets:
            tmp1=deepcopy(tmp0[childsubsets[ik][0]])
            #
            noprint=("Type of calculation" in tmp1['key'] or "Convergence" in tmp1['key'] or "TEM-TSH" in tmp1['key']) and istorsrun
            #
            if(tmp1['props']!=[]):
                if not noprint:
                    llog.append(str(tmp1['key'])+" : "+str(tmp1['name'])+ " = {")
                tmp2=tmp1['props']
                for ij in range(len(tmp2)):
                        #llog.append(str(tmp2[ij]['name'])+" : "+str(tmp2[ij]['values'][0]))
                        #
                        if('valueLabels' in tmp2[ij]):
                            ival=[k0 for k0,v0 in tmp2[ij]['valueLabels'].items() if v0==tmp2[ij]['values'][0]][0]
                            if not (noprint or ('visible' in tmp2[ij] and tmp2[ij]['visible']==False)):
                                llog.append(str(tmp2[ij]['name'])+" : "+str(ival))
                        else:
                            #
                            if not (noprint or 'visible' in tmp2[ij] and tmp2[ij]['visible']==False):
                                llog.append(str(tmp2[ij]['name'])+" : "+str(tmp2[ij]['values'][0]))

                if not noprint:
                    llog.append("}")
            #
            else:
                if not noprint:
                    llog.append(str(tmp1['key'])+" : "+str(tmp1['name']))
            #



    def prepWriteThermoMecaProps(self,propatts,propents,propvalents,proppgs,propvalpgs,propstrs,llog,iflag):

        llog.append("");llog.append("############### List of MATERIALS already defined (not necessarily assigned to entities/physgroups) ###############")
        for i in range(len(self.listMats)):
            imatstr=list(self.listMats[i].keys())[0]
            iprops=list(self.listMats[i].values())[0]
            tmpstr,fullname=imatstr.split("/")
            iname,idim=tmpstr.split(';')
            idim=int(idim)
            igroup,isafirname=fullname.replace('New Material Definition-','').split('-')
            #
            if(iflag==1):
                llog.append(" - \""+iname+"\" (gmsafir name) - "+self.allShapes[idim]+":")
                llog.append("          - SAFIR name: \""+isafirname+"\"")
                llog.append("          - Material Group: \""+igroup+"\"")
                for iprop in iprops:
                    propname=list(iprop.keys())[0]
                    pattern=re.compile("^[0-9]+")
                    if not "torsname" in propname and not "New Material Name" in propname:
                        if(re.search(pattern, propname)!=None):
                            propname=propname.replace(re.search(pattern, propname).group(0),'')
                        propval=list(iprop.values())[0][0]
                        llog.append("          - "+propname+" - value="+str(propval))
            #
            else:
                llog.append(self.allShapes[idim]+" - New Material Definition : "+iname+" = {")
                llog.append("Material Name : "+str(isafirname))
                llog.append("Material Group Name : "+str(igroup))
                for iprop in iprops:
                    propname=list(iprop.keys())[0]
                    pattern=re.compile("^[0-9]+")
                    if not "torsname" in propname and not "New Material Name" in propname:
                        if(re.search(pattern, propname)!=None):
                            propname=propname.replace(re.search(pattern, propname).group(0),'')
                        propval=list(iprop.values())[0][0]
                        llog.append(propname+" : "+str(propval))
                llog.append("}");llog.append("")
        #
        llog.append("");llog.append("############### List of LAX already defined (not necessarily assigned to entities/physgroups) ###############")
        #
        for i in range(len(self.listLAX)):
            ilaxstr=list(self.listLAX[i].keys())[0]
            iprops=list(self.listLAX[i].values())[0]
            tmpstr,fullname=ilaxstr.split("/")
            iname,idim=tmpstr.split(';')
            idim=int(idim)
            #
            if(iflag==1):
                llog.append(" - \""+iname+"\" (gmsafir name) - "+self.allShapes[idim]+":")
                for iprop in iprops:
                    propname=list(iprop.keys())[0]
                    pattern=re.compile("^[0-9]+")
                    if not "New LAX Name" in propname:
                        if(re.search(pattern, propname)!=None):
                            propname=propname.replace(re.search(pattern, propname).group(0),'')
                        propval=list(iprop.values())[0][0]
                        llog.append("          - "+propname+" - value="+str(propval))
            #
            else:
                llog.append(self.allShapes[idim]+" - New LAX Definition : "+iname+" = {")
                for iprop in iprops:
                    propname=list(iprop.keys())[0]
                    pattern=re.compile("^[0-9]+")
                    if not "New LAX Name" in propname:
                        if(re.search(pattern, propname)!=None):
                            propname=propname.replace(re.search(pattern, propname).group(0),'')
                        propval=list(iprop.values())[0][0]
                        llog.append(propname+" : "+str(propval))
                llog.append("}");llog.append("")
        #
        llog.append("");llog.append("############### PROPERTIES assigned to Entities ###############")
        #
        if(iflag==1):
            for k,v in propents.items():
                if(v!=[]):
                    inam,idim=k.split(';')
                    idim=int(idim)
                    ifullname=[iflnm for (ik,iflnm) in propstrs if ik==k][0]
                    llog.append(" - "+ifullname+" : ")
                    for i in range(len(v)):
                        llog.append("          - "+self.allShapes[idim]+" "+str(v[i])+" : "+str(propvalents[k][i]))
        else:
            for k,v in propatts.items():
                if(v!={}):
                    inam,idim=k.split(';')
                    idim=int(idim)
                    ifullname=[iflnm for (ik,iflnm) in propstrs if ik==k][0]
                    for k0,v0 in v.items():
                        if('ents' in v0):
                            llog.append(self.allShapes[idim]+" - "+ifullname+"("+self.allShapes[idim]+" "+str(v0['ents'][0])+") = {")
                            for ik in range(len(v0['props'])):
                                iprop=v0['props'][ik]
                                propnam=list(iprop.keys())[0]
                                j0=[j for j in range(len(v0["defaultprops"])) if v0["defaultprops"][j]['name']==propnam][0]
                                idefprops=v0['defaultprops'][j0]
                                ikey=list(iprop.keys())[0]
                                ival0=list(iprop.values())[0][0]
                                pattern=re.compile("^[0-9]+")
                                if(re.search(pattern, ikey)!=None):
                                    ikey=ikey.replace(re.search(pattern, ikey).group(0),'')
                                if('valueLabels' in idefprops):
                                    ival=[k1 for k1,v1 in idefprops['valueLabels'].items() if ival0==v1][0]
                                    if not ("visible" in idefprops and idefprops['visible']==False):
                                        llog.append(ikey+" : "+str(ival))
                                else:
                                    if not ("visible" in idefprops and idefprops['visible']==False):
                                        llog.append(ikey+" : "+str(ival0))

                            llog.append("}");llog.append("")

        llog.append("");llog.append("############### PROPERTIES assigned to Groups ###############")
        #
        if(iflag==1):
            for k,v in proppgs.items():
                if(v!=[]):
                    inam,idim=k.split(';')
                    idim=int(idim)
                    ifullname=[iflnm for (ik,iflnm) in propstrs if ik==k][0]
                    llog.append(" - "+ifullname+" : ")
                    for i in range(len(v)):
                        llog.append("          - Physical "+self.allShapes[idim]+" "+str(v[i])+" : "+str(propvalpgs[k][i]))
        else:
            for k,v in propatts.items():
                if(v!={}):
                    inam,idim=k.split(';')
                    idim=int(idim)
                    ifullname=[iflnm for (ik,iflnm) in propstrs if ik==k][0]
                    for k0,v0 in v.items():
                        if('pgs' in v0):
                            llog.append(self.allShapes[idim]+" - "+ifullname+"(Physical "+self.allShapes[idim]+" "+str(v0['pgs'][0])+") = {")
                            for ik in range(len(v0['props'])):
                                iprop=v0['props'][ik]
                                propnam=list(iprop.keys())[0]
                                j0=[j for j in range(len(v0["defaultprops"])) if v0["defaultprops"][j]['name']==propnam][0]
                                idefprops=v0['defaultprops'][j0]
                                ikey=list(iprop.keys())[0]
                                ival0=list(iprop.values())[0][0]
                                pattern=re.compile("^[0-9]+")
                                if(re.search(pattern, ikey)!=None):
                                    ikey=ikey.replace(re.search(pattern, ikey).group(0),'')
                                if('valueLabels' in idefprops):
                                    ival=[k1 for k1,v1 in idefprops['valueLabels'].items() if ival0==v1][0]
                                    if not ("visible" in idefprops and idefprops['visible']==False):
                                    #if(1>0):
                                        llog.append(ikey+" : "+str(ival))
                                else:
                                    if not ("visible" in idefprops and idefprops['visible']==False):
                                    #if(1>0):
                                        llog.append(ikey+" : "+str(ival0))

                            llog.append("}");llog.append("")
            #




    def viewAndWriteInfog4s(self,iflag):
        pattern=re.compile("[0-9]")
        ndims=int(re.search(pattern, self.pbType).group(0))
        #ndims=int(re.search(pattern, myapp.pbType).group(0))
        print("Enter viewAndWrite")
        do_regroup=False
        #
        listlog=[]
        #
        # Create listProps
        rc,PropAtts,PropPgs,PropEnts,PropValPgs,PropValEnts,PropExtValEnts,PropExtValPgs,propstrs,_,_,_,_=self.listProps(ndims,do_regroup)

        #DISPLAY ALL in ONE:
        listlog.append("");listlog.append("")
        listlog.append('##########################################################################################################')
        listlog.append('################################## GENERAL PROPERTIES ####################################################')
        listlog.append('##########################################################################################################')
        # Print the set of properties in safirDB (select pbType)
        listlog.append("Problem Type: "+str(self.pbType))
        self.prepWriteGenProps(listlog,iflag)
        listlog.append("");listlog.append("")
        listlog.append('##########################################################################################################')
        listlog.append('################################## THERMO-MECHANICAL PROPERTIES ###########################################')
        listlog.append('##########################################################################################################')
        self.prepWriteThermoMecaProps(PropAtts,PropEnts,PropExtValEnts,PropPgs,PropExtValPgs,propstrs,listlog,iflag)
        # Print the set of properties in contextDB (get from PropAtts)x
        listlog.append("");listlog.append("")
        #
        if iflag==1: #Write to log window
            for ilog in listlog:
                gmsh.logger.write(ilog, level="info")
        #
        else: # Write down to G4S file
            if self.g4sfileError=="":
                with open(self.g4sfile, 'w') as f:
                    for ilog in listlog:
                        f.write(ilog+"\n")
            else:
                gmsh.logger.write("Still errors in reading G4S file - cannot over-write!!", level="error")



    def removeViewTag(self,idx):
        vtags=gmsh.view.getTags()
        if(list(vtags)!=[]):
            if(idx in vtags):
                gmsh.view.remove(idx)


    def cleaningToClean(self):
        # clean previous colors, names, and variables Geometry.XXXNumbers and Geometry.LabelType
        if(self.toClean!={}):
            #
            if("colors" in self.toClean):
                for ikey,irgba in self.toClean["colors"].items():
                    idim,itag=ikey.split("\t")
                    gmsh.model.setColor([(int(idim),int(itag))], irgba[0], irgba[1], irgba[2], irgba[3], True)
            #
            if("names" in self.toClean):
                for ikey,ival in self.toClean["names"].items():
                    idim,itag=ikey.split("\t")
                    gmsh.model.setEntityName(int(idim), int(itag), ival)
            #
            keyslbls=[k for k,v in self.toClean.items() if 'geomlbls' in k]
            if(keyslbls!=[]):
                for ikey in keyslbls:
                    _,ishp=ikey.split("\t")
                    gmsh.option.setNumber('Geometry.'+ishp+'Numbers', self.toClean[ikey])
            #
            if('geomlbltype' in self.toClean):
                gmsh.option.setNumber('Geometry.LabelType',self.toClean['geomlbltype'])

        self.toClean={}

        self.removeViewTag(self.legendtag)
        self.removeViewTag(self.LAXtag)


    def manageInspect(self,ctyp):
        #
        self.updateGeneralLists()
        # clean previous colors, names, and variables Geometry.XXXNumbers and Geometry.LabelType
        self.cleaningToClean()
        #
        inspectColors={}
        inspectColors['mats']=[(255,0,0),(255,8,189),(288,97,100),(82,8,255),(8,99,255),(8,230,255),(8,255,156),(8,255,41),(156,255,8),(255,255,0),(255,214,8)]
        inspectColors['beamcormat']=inspectColors['mats']
        inspectColors['beamlax']=inspectColors['mats']
        inspectColors['trusscormat']=inspectColors['mats']
        inspectColors['shcormat']=inspectColors['mats']
        inspectColors['solcormat']=inspectColors['mats']
        inspectColors['flxs']=[(247,21,217),(247,21,217),(247,21,217),(247,21,217),(247,21,217),(247,21,217)]
        inspectColors['frtiers']=[(195,21,247),(195,21,247),(195,21,247),(195,21,247),(195,21,247)]
        inspectColors['blks']=[(250,211,142),(250,211,142),(250,211,142),(250,211,142),(250,211,142)]
        inspectColors['beamrelax']=[(250,211,142),(250,211,142),(250,211,142),(250,211,142),(250,211,142)]
        #
        inspectColors['same']=[(250,211,142),(250,211,142),(250,211,142),(250,211,142),(250,211,142)]
        #
        if("Structural" in self.pbType):
            inspectColors['sload']=[(255,0,0),(255,8,189),(288,97,100),(82,8,255),(8,99,255),(8,230,255),(8,255,156),(8,255,41),(156,255,8),(255,255,0),(255,214,8)]
            inspectColors['hydrostat']=[(255,0,0),(255,8,189),(288,97,100),(82,8,255),(8,99,255),(8,230,255),(8,255,156),(8,255,41),(156,255,8),(255,255,0),(255,214,8)]
            inspectColors['tlload']=[(255,0,0),(255,8,189),(288,97,100),(82,8,255),(8,99,255),(8,230,255),(8,255,156),(8,255,41),(156,255,8),(255,255,0),(255,214,8)]
            inspectColors['tgload']=[(255,0,0),(255,8,189),(288,97,100),(82,8,255),(8,99,255),(8,230,255),(8,255,156),(8,255,41),(156,255,8),(255,255,0),(255,214,8)]
            inspectColors['mass']=[(250,211,142),(250,211,142),(250,211,142),(250,211,142),(250,211,142)]
        #
        if(self.pbType=="Thermal 2D"):
            inspectColors['void']=[(71,71,71),(102,102,102),(146,146,146),(210,210,210)]
            if(self.nvoids>0):
                inspectColors['void_sym']=[(71,71,71),(102,102,102),(146,146,146),(210,210,210)]
            inspectColors['real_sym']=[(255,255,0),(255,255,0),(255,255,0),(255,255,0),(255,255,0)]
            inspectColors['tors']=[(255,204,204),(255,204,204),(255,204,204),(255,204,204),(255,204,204)]
        #
        pattern=re.compile("[0-9]")
        ndims=int(re.search(pattern, self.pbType).group(0))

        do_regroup=True
        rc,PropAtts,PropPgs,PropEnts,PropValPgs,PropValEnts,PropExtValEnts,PropExtValPgs,propstrs,ishptyp,ishptypm,nmats,uniqmatlist=self.listProps(ndims,do_regroup)
        if(rc!=0):
            return rc
        #
        ctyps={'materials':'mats','fluxes':'flxs',
               'frontiers':'frtiers','tblocks':'tors',
               'blocks':'blks','voids':'void','realsym':'real_sym',
               'lax':'lax','loads':'loads','same':'same','mass':'mass',
               'relax':'beamrelax'}

        ugtyps=[]

        if not ("blks" in ctyps[ctyp] or "void" in ctyps[ctyp]) :
            #ugtyps.append(ctyps[ctyp])
            ugtyps=[igtypdim for igtypdim,v in PropEnts.items() if ctyps[ctyp] in igtypdim]
            #
            # Special cases
            if("mats" in ctyps[ctyp] and self.isThermal==False):
                ugtyps=[igtypdim for igtypdim,v in PropEnts.items() if 'beamcormat' in igtypdim or 'shcormat' in igtypdim or 'trusscormat' in igtypdim or 'solcormat' in igtypdim]
            elif "lax" in ctyps[ctyp] and not "relax" in ctyps[ctyp]:
                ugtyps=[igtypdim for igtypdim,v in PropEnts.items() if 'beamlax' in igtypdim]
            elif "loads" in ctyps[ctyp]:
                ugtyps=[igtypdim for igtypdim,v in PropEnts.items() if "load" in igtypdim or "hydrostat" in igtypdim]
            #
        elif "void" in ctyps[ctyp]:
            ugtyps=[igtypdim for igtypdim,v in PropEnts.items() if "void" in igtypdim]
        elif "tors" in ctyps[ctyp]:
            ugtyps=[igtypdim for igtypdim,v in PropEnts.items() if "tors" in igtypdim]
        else:
            ugtyps=[igtypdim for igtypdim,v in PropEnts.items() if "blks" in igtypdim and not "tors" in igtypdim]

        notdef=0

        for ugtypdim in ugtyps:
            print(ugtypdim,PropEnts[ugtypdim])
            #
            listvals=list(set(PropExtValEnts[ugtypdim]))
            #
            if(len(PropEnts[ugtypdim])!=0):
                nugtyps=len(PropEnts[ugtypdim])
                for i in range(nugtyps):
                    itag=int(PropEnts[ugtypdim][i])
                    ugtyp,idim=ugtypdim.split(';')
                    idim=int(idim)
                    ishp=self.allShapes[idim]
                    ival=PropExtValEnts[ugtypdim][i]
                    irgb=inspectColors[ugtyp][listvals.index(ival)]

                    # save previous color before changing (in order to clean later)
                    if(not 'colors' in self.toClean):
                        self.toClean['colors']={}
                    if not str(idim)+"\t"+str(itag) in self.toClean['colors']:
                        self.toClean['colors'][str(idim)+"\t"+str(itag)]=gmsh.model.getColor(idim,itag)
                    #
                    gmsh.model.setColor([(idim,itag)], irgb[0], irgb[1], irgb[2], 255, True)

                    ival0=gmsh.model.getEntityName(idim, itag)
                    ival=str(ival)

                    #
                    if "lax" in ctyps[ctyp] and not "relax" in ctyps[ctyp]:
                        print('ival=',ival)
                        self.LAXspecial=True
                        print("self.listLAX=",self.listLAX)
                        self.laxid=[k for k in range(len(self.listLAX)) if ival+";1" in list(self.listLAX[k].keys())[0]][0]
                        #
                        if(i==0):
                            self.LAXspecial=True
                        if(i==1):
                            self.ViewLAXOnce=False
                        if(i==nugtyps-1):
                            self.finalDrawLAX=True
                        #

                        self.isViewLAX=True
                        (xp0,yp0,zp0)=self.recreateLAXView("Curve "+str(itag))
                        self.isViewLAX=False
                        #
                        if(i==nugtyps-1):
                            self.finalDrawLAX=False
                            self.ViewLAXOnce=True
                            self.LAXspecial=False
                    #
                    elif("mats" in ctyps[ctyp] and self.isThermal==False):
                        if ugtypdim == "shcormat;2":
                            ival=ival.split(' - ')[0]+' - '+ival.split(' - ')[1]+' - '+ival.split(' - ')[2]
                            ival="shell:"+ival
                        #
                        elif ugtypdim == "trusscormat;1":
                            if(ival0==""):
                                ival='truss: '+ival.split(' - ')[0]+' - '+ival.split(' - ')[1]+' - '+ival.split(' - ')[2]+' - '+ival.split(' - ')[3]
                            else:
                                ival=ival0+'; truss: '+ival.split(' - ')[0]+' - '+ival.split(' - ')[1]+' - '+ival.split(' - ')[2]+' - '+ival.split(' - ')[3]
                        #
                        elif ugtypdim == "beamcormat;1":
                            if(ival0==""):
                                ival='beam: '+ival.split(' - ')[0]+' - '+ival.split(' - ')[1]
                            else:
                                ival=ival0+'; beam: '+ival.split(' - ')[0]+' - '+ival.split(' - ')[1]
                        #
                        elif ugtypdim == "solcormat;3":
                            ival="solid: "+ival
                        #
                        else:
                            ival=ival.split(' - ')[0]+' - '+ival.split(' - ')[1]
                    #
                    elif("loads" in ctyps[ctyp]):
                        print ("loads: ",ugtypdim)
                        if ugtypdim == "sload;0":
                            if(ival0==""):
                                ival="nodeload: "+ival
                            else:
                                ival=ival0+"; nodeload: "+ival
                        elif ugtypdim == "sload;1":
                            if(ival0==""):
                                ival="distrbeam: "+ival
                            else:
                                ival=ival0+"; distrbeam: "+ival
                        elif ugtypdim == "sload;2":
                            if(ival0==""):
                                ival="distrshell: "+ival
                            else:
                                ival=ival0+"; distrshell: "+ival
                        elif ugtypdim == "tgload;1":
                            if(ival0==""):
                                ival="trapglobm: "+ival
                            else:
                                ival=ival0+"; trapglobm: "+ival
                        elif ugtypdim == "tlload;1":
                            if(ival0==""):
                                ival="traplocm: "+ival
                            else:
                                ival=ival0+"; traplocm: "+ival
                        elif ugtypdim == "hydrostat;1":
                            if(ival0==""):
                                ival="hydrostat: "+ival
                            else:
                                ival=ival0+"; hydrostat: "+ival
                    #
                    # save previous entity name before changing (in order to clean later)
                    if(not 'names' in self.toClean):
                        self.toClean['names']={}
                    if not str(idim)+"\t"+str(itag) in self.toClean['names']:
                        self.toClean['names'][str(idim)+"\t"+str(itag)]=gmsh.model.getEntityName(idim,itag)
                    #
                    gmsh.model.setEntityName(idim, itag, ival)

                # save previous status before changing (in order to clean later)
                if(not 'geomlbls\t'+ishp in self.toClean):
                    self.toClean['geomlbls\t'+ishp]=gmsh.option.getNumber('Geometry.'+ishp+'Numbers')
                gmsh.option.setNumber('Geometry.'+ishp+'Numbers', 1) # SurfaceLabels ne fonctionne que sous Linux, pas sous Windows!

                # save previous status before changing (in order to clean later)
                if(not 'geomlbltype' in self.toClean):
                    self.toClean['geomlbltype']=gmsh.option.getNumber('Geometry.LabelType')
                gmsh.option.setNumber('Geometry.LabelType',3)
            else:
                notdef+=1
        if(notdef==len(ugtyps)):
            self.removeViewTag(self.legendtag)
            gmsh.logger.write("No "+ctyp+" properties yet defined", level="error")
            return 0
        #
        if("mats" in ctyps[ctyp]):
            self.removeViewTag(self.legendtag)
            vtags=gmsh.view.getTags()
            #if(vtags==[] or not self.legendtag in vtags):
            if(list(vtags)==[] or not self.legendtag in vtags):
                t1 = gmsh.view.add("Materials LEGEND",self.legendtag)
                # Create mats legend from uniqmatlist:
                gmsh.view.addListDataString(self.legendtag, [20., -700.], ["LEGEND"])
                for i in range(len(self.listMats)):
                    tmpmat=list(self.listMats[i].keys())[0]
                    imat=tmpmat.split('/')[0].split(";")[0]
                    imat+=" - "+tmpmat.split('/')[1].replace('New Material Definition-','')
                    ioffset=20*(i+1)
                    gmsh.view.addListDataString(self.legendtag, [20., -700.+ioffset], [str(i+1)+" : "+imat])
        #
        elif("lax" in ctyps[ctyp] and not "relax" in ctyps[ctyp]):
            self.removeViewTag(self.legendtag)
            vtags=gmsh.view.getTags()
            if(list(vtags)==[] or not self.legendtag in vtags):
                t1 = gmsh.view.add("Local Axes LEGEND",self.legendtag)
                # Create mats legend from uniqmatlist:
                gmsh.view.addListDataString(self.legendtag, [20., -700.], ["LEGEND"])
                for i in range(len(self.listLAX)):
                    ilax=list(self.listLAX[i].keys())[0].split('/')[0].split(";")[0]
                    ioffset=20*(i+1)
                    gmsh.view.addListDataString(self.legendtag, [20., -700.+ioffset], [str(i+1)+" : "+ilax])
        #
        else:
            self.removeViewTag(self.legendtag)
        #
        return 0


# Creation of SAFIR input file (.IN)
# Notes:
# - 2D: user creates its model in a coordinate system with XY axes (initial config for GMSH), and G4S rotates automatically in a coordinate system with YZ axes (those of SAFIR)
#
    def verifyRectangleSingleEntity(self,shpedges,ient,ipg):
        #
        if(len(shpedges)!=4):
            if(ipg!="-1"):
                gmsh.logger.write("Entity "+ient+" in 'Physical Surface "+ipg+"' should have 4 corners in TSH simulation", level="error")
            else:
                gmsh.logger.write("Entity "+ient+" should have 4 corners for TSH simulation", level="error")
            return -1
        #
        x=[];y=[];z=[]
        for ie in range(4):
            inode=abs(int(shpedges[ie][1]))
            tmp=gmsh.model.getValue(0, inode,[])
            x.append(tmp[0]);y.append(tmp[1]);z.append(tmp[2])
        #
        if(max(z)!=0):
            if(ipg!="-1"):
                gmsh.logger.write("Entity "+ient+" in 'Physical Surface "+ipg+"' must be defined in the XY plane for TSH simulation", level="error")
            else:
                gmsh.logger.write("Entity "+ient+" must be defined in the XY plane for TSH simulation", level="error")
            return -1
        #
        # center of mass
        cx=0;cy=0
        for ie in range(4):
            cx+=x[ie]/4
            cy+=y[ie]/4
        # rectangle: all distances btw point and center of mass must be equals
        dd=[]
        for ie in range(4):
            dd.append(math.pow(x[ie]-cx,2)+math.pow(y[ie]-cy,2))

        def isDistEqual(d1,d2):
            isequal=False
            if(abs(d1-d2)/(abs(d1)+1e-20)<1e-6):
                isequal=True
            return isequal

        if not (isDistEqual(dd[0],dd[1]) and isDistEqual(dd[1],dd[2]) and isDistEqual(dd[2],dd[3])):
            if(ipg!="-1"):
                gmsh.logger.write("Entity "+ient+" in 'Physical Surface "+ipg+"' must be a rectangle", level="error")
            else:
                gmsh.logger.write("Entity "+ient+" must be a rectangle", level="error")
            return -1
        #
        return 0


    def verifyRectangleGeomTSH(self,propPgsMats,propEntsMats):
        print('Verify Geometry for TSH calculation')
        #
        idim=2
        try:
            # Test the entities in the physgroups
            if(propPgsMats!=[]):
                for i in range(len(propPgsMats)):
                    ipg=propPgsMats[i]
                    for ient in gmsh.model.getEntitiesForPhysicalGroup(idim, int(ipg)):
                        rc=self.verifyRectangleSingleEntity(gmsh.model.getBoundary([(idim, int(ient))],recursive=True),ient,ipg)
            # Test the other entities
            if(propEntsMats!=[]):
                for i in range(len(propEntsMats)):
                    ient=propEntsMats[i]
                    rc=self.verifyRectangleSingleEntity(gmsh.model.getBoundary([(idim, int(ient))],recursive=True),ient,"-1")

        except Exception as emsg:
            gmsh.logger.write("Problem in verifyRectangleGeomTSH:"+str(emsg), level="error")
            return -1
        return 0


    def isLineEntityCollinearWithAxis(self,ientm,ivect):
        collin0=False
        ipts=gmsh.model.getBoundary([(1, int(ientm))])
        #
        x=[];y=[]
        for ie in range(2):
            inode=abs(int(ipts[ie][1]))
            tmp=gmsh.model.getValue(0, inode,[])
            x.append(tmp[0]);y.append(tmp[1])
        #
        u=[];u.append(x[1]-x[0]);u.append(y[1]-y[0])
        #
        # Determinant:
        idet=ivect[1]*u[0]-ivect[0]*u[1]
        if(abs(idet)<1e-6):
            collin0=True
        #
        return collin0


    def verifMeshTSH(self,propPgsMats,propEntsMats,meshEntityTags):
        print('Verify Mesh for TSH calculation...')
        idim=2
        try:
            # Test the entities in the physgroups
            if(propPgsMats!=[]):
                for i in range(len(propPgsMats)):
                    ipg=propPgsMats[i]
                    for ient in gmsh.model.getEntitiesForPhysicalGroup(idim, int(ipg)):
                        for idimm,ientm in gmsh.model.getBoundary([(idim, int(ient))]):
                            #Verify number of mesh elems if aligned with X-axis
                            if self.isLineEntityCollinearWithAxis(abs(ientm),[1,0,0]):
                                tmp=[]
                                for imsh in meshEntityTags:
                                    if(imsh==abs(ientm)):
                                        tmp.append(imsh)
                                if(len(tmp)!=1):
                                    raise ValueError("Pb in meshing: Entity "+str(ientm)+" aligned with X-axis shall have only 1 mesh element")
            #
            # Test the other entities
            if(propEntsMats!=[]):
                for i in range(len(propEntsMats)):
                    ient=propEntsMats[i]
                    for idimm,ientm in gmsh.model.getBoundary([(idim, int(ient))]):
                            #Verify number of mesh elems if aligned with X-axis
                            if self.isLineEntityCollinearWithAxis(abs(ientm),[1,0,0]):
                                tmp=[]
                                for imsh in meshEntityTags:
                                    if(imsh==abs(ientm)):
                                        tmp.append(imsh)
                                if(len(tmp)!=1):
                                    raise ValueError("Pb in meshing: Entity "+str(abs(ientm))+" aligned with X-axis shall have only 1 mesh element")
        #
        except Exception as emsg:
            gmsh.logger.write("Problem in verifMeshTSH:"+str(emsg), level="error")
            return -1
        #
        print('Verify Mesh for TSH calculation... OK')
        #
        return 0


    def reOrderMeshBordersTSH(self,iborder0,ntags,ncoords):
        #
        ibordercoords=[]
        iborder=deepcopy(iborder0)
        for i in range(len(iborder)):
            j=ntags.index(iborder[i])
            ibordercoords.append(ncoords[3*j+1]) #Only y-coordinate is needed

        def aInfb(i,j):
            isthecase=False
            ya=ibordercoords[i]
            yb=ibordercoords[j]
            if(ya<yb):
                isthecase=True
            return isthecase
        #
        #Sort the array in ascending order
        for i in range(0, len(iborder)):
            for j in range(i+1, len(iborder)):
                if(aInfb(j,i)):
                    temp = iborder[i]
                    iborder[i] = iborder[j]
                    iborder[j] = temp
                    temp2=ibordercoords[i]
                    ibordercoords[i] = ibordercoords[j]
                    ibordercoords[j] = temp2
        #
        return iborder


    def specialNodeNumberingTSH(self,propPgsMats,propEntsMats,meshEntityTags,meshNodeTags,nTags,nCoords):
        cornodes=[]
        print('Renumbering (TSH has a special numbering of nodes)...')
        idim=2
        try:
            allMeshesp=[] # Collect the lines on the right vertical border
            allMeshesm=[] # Collect the lines on the left vertical border
            #
            # Test the entities in the physgroups
            if(propPgsMats!=[]):
                for i in range(len(propPgsMats)):
                    ipg=propPgsMats[i]
                    for ient in gmsh.model.getEntitiesForPhysicalGroup(idim, int(ipg)):
                        xmin2D,_,_,xmax2D,_,_=gmsh.model.getBoundingBox(2, ient)
                        for idimm,ientm in gmsh.model.getBoundary([(idim, int(ient))]):
                            #Verify number of mesh elems if aligned with X-axis
                            if self.isLineEntityCollinearWithAxis(abs(ientm),[0,1,0]):
                                xmin1D,_,_,xmax1D,_,_=gmsh.model.getBoundingBox(1, abs(ientm))
                                if(abs((xmin1D-xmin2D)/(abs(xmin2D)+1e-20))<0.05):
                                    allMeshesm.append(abs(ientm))
                                else:
                                    allMeshesp.append(abs(ientm))
            #
            #
            # Test the other entities
            if(propEntsMats!=[]):
                for i in range(len(propEntsMats)):
                    ient=propEntsMats[i]
                    xmin2D,_,_,xmax2D,_,_=gmsh.model.getBoundingBox(2, int(ient))
                    for idimm,ientm in gmsh.model.getBoundary([(idim, int(ient))]):
                        #Verify number of mesh elems if aligned with X-axis
                        if self.isLineEntityCollinearWithAxis(abs(ientm),[0,1,0]):
                            xmin1D,_,_,xmax1D,_,_=gmsh.model.getBoundingBox(1, abs(ientm))
                            if(abs((xmin1D-xmin2D)/(abs(xmin2D)+1e-20))<0.05):
                                allMeshesm.append(abs(ientm))
                            else:
                                allMeshesp.append(abs(ientm))
            #
            # Reorder elements in allMeshesm and allMeshesp
            if(allMeshesp!=[] and allMeshesm!=[]):
                #allMeshesp=self.reOrderMeshBordersTSH(allMeshesp,nTags,nCoords)
                #allMeshesm=self.reOrderMeshBordersTSH(allMeshesm,nTags,nCoords)!
                meshnodesp=[];meshnodesm=[]
                for i in allMeshesp:
                    for imsh in range(len(meshEntityTags)):
                        if(meshEntityTags[imsh]==i):
                            meshnodesp+=meshNodeTags[imsh]

                for i in allMeshesm:
                    for imsh in range(len(meshEntityTags)):
                        if(meshEntityTags[imsh]==i):
                            meshnodesm+=meshNodeTags[imsh]

                meshnodesm=list(set(meshnodesm))
                meshnodesp=list(set(meshnodesp))
                meshnodespO=self.reOrderMeshBordersTSH(meshnodesp,nTags,nCoords)
                meshnodesmO=self.reOrderMeshBordersTSH(meshnodesm,nTags,nCoords)

                cornodes=[]
                for i in range(len(meshnodesmO)):
                    cornodes.append(nTags.index(meshnodesmO[i]))
                for i in range(len(meshnodespO)):
                    cornodes.append(nTags.index(meshnodespO[i]))

            else:
                raise ValueError("Pb in TSH geometry: Could not collect the left and right borders")
        #
        except Exception as emsg:
            gmsh.logger.write("Problem in specialNodeNumberingTSH:"+str(emsg), level="error")
            return -1,cornodes
        #
        print('Renumbering (TSH has a special numbering of nodes)... OK')
        return 0,cornodes



    def mergeSameIdx(self,s0):
        #
        s=s0
        notfinal=True
        initstep=True
        newidx=[]
        #
        while(notfinal):
            keys={}
            for k in range(len(s)):
                i,v=s[k].split("/")
                if i in keys:
                    keys[i].append(k)
                else:
                    keys[i]=[k]
            #
            testisfinal=True
            #
            if(initstep):
                n=0
                for k,tab in keys.items():
                    for i in range(len(tab)):
                        newidx.append(tab[i])
                initstep=False
            snew=[]
            for k,tab in keys.items():
                tabi=[tab[i] for i in range(len(tab)) if len(s[tab[i]].split("/")[1].split(";"))>1]
                if(tabi!=[]):
                    testisfinal=False
                    i1=tabi[0] # first with 2 indexes
                    #
                    part1=s[i1].split("/")[0]
                    part2=s[i1].split("/")[1]
                    ri1=part2.split(";")[0]
                    ri2=part2.split(";")[1]
                    #print('ri1,ri2=',ri1,ri2)
                    #
                    for i in range(len(tab)):
                        parttmp2=s[tab[i]].split("/")[1].split(";")
                        #print('parttmp2=',parttmp2)
                        parttmp3tab=[]
                        for m0 in parttmp2:
                            if(m0==ri1):
                                parttmp3tab.append(ri2)
                            elif(m0==ri2):
                                parttmp3tab.append(ri2)
                            elif(m0!=ri2):
                                parttmp3tab.append(m0)
                        parttmp3tab=list(set(parttmp3tab))
                        parttmp3=';'.join(parttmp3tab)
                        snew.append(part1+"/"+parttmp3)
                        #print('parttmp3=',part1+"/"+parttmp3)
                else:
                    for i in range(len(tab)):
                        snew.append(s[tab[i]])
            s=snew
                #
            notfinal=not testisfinal

        sfinal=[]
        for i in range(len(newidx)):
            sfinal.append(snew[newidx.index(i)])
        return(sfinal)


    def verifyQuads(self,pents,ppgs,meshEntityTags,meshNodeTags):
        rc=0

        # Test the entities in the physgroups
        idim=2
        if(ppgs!=[]):
            for i in range(len(ppgs)):
                ipg=ppgs[i]
                for ient in gmsh.model.getEntitiesForPhysicalGroup(idim, int(ipg)):
                    for imsh in range(len(meshEntityTags)):
                        if meshEntityTags[imsh]==ient:
                            if(len(meshNodeTags[imsh])!=4):
                                gmsh.logger.write("Having Shells in your geometry, you need to force the 2Dmeshing to be composed only of quads: use Mesh/Recombine2D when meshing.", level="error")
                                return -1
        #
        # Test the other entities
        if(pents!=[]):
            for i in range(len(pents)):
                ient=pents[i]
                for imsh in range(len(meshEntityTags)):
                        if meshEntityTags[imsh]==ient:
                            if(len(meshNodeTags[imsh])!=4):
                                gmsh.logger.write("Having Shells in your geometry, you need to force the 2Dmeshing to be composed only of quads: use Mesh/Recombine2D when meshing.", level="error")
                                return -1
        return rc


    def createIN(self):
        #print('Create SAFIR .IN file with the given parameters...')

        gmsh.logger.write("Create SAFIR .IN file with the given parameters...", level="info")

        gmsh.model.geo.synchronize()

        # Verification: Test that previous step (meshing) has been done
        try:
            entities = gmsh.model.getEntities()
            elemTags=[]

            for e in entities:
                elemTypes, elemTags, elemNodeTags = gmsh.model.mesh.getElements(1, -1)
            if(elemTags==[]):
                raise ValueError("Mesh not yet generated - Generate it")
        except Exception as emsg:
                gmsh.logger.write("Problem in entity collections:"+str(emsg), level="error")
                return -1
        #
        # Get from contextDB the thermal properties of the different entities/physgroups - TBD : check that each entity/phys group has only one property type (Material,...)
        pattern=re.compile("[0-9]")
        ndims=int(re.search(pattern, self.pbType).group(0))

        do_regroup=False
        rc,PropAtts,PropPgs,PropEnts,PropValPgs,PropValEnts,PropExtValEnts,PropExtValPgs,propstrs,ishptyp,ishptypm,nmats,uniqmatlist=self.listProps(ndims,do_regroup)
        if(rc!=0):
            return rc

        # TBD - Verification on entities/physgroups:check that each entity/phys group has only one property type (Material,...)

        # Verifications for Thermal:
        istorsrun=False
        istsh=False
        #
        if(self.isThermal):
            # Verification on entities/physgroups: Test if existing block for Torsion run

            if(ndims==2):
                tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","Run torsion analysis")],False)
                istorsrun=tmp0["values"]==[1]
                if istorsrun and PropAtts['tors;0']=={}:
                    gmsh.logger.write("For Torsion run, you need to define at least 1 point 'Torsion Point Constraint'", level="error")
                    return -1

            # Verification on entities/physgroups: Test, when present, that the symvoids and realsym are point physgroup and contain only 2 points
            if(ndims==2):
                if(PropPgs['real_sym;1']!=[]):
                    gmsh.logger.write("A 'Physical Curve' cannot get a 'Real SymAxis Constraint'", level="error")
                    return -1
                #
                if(PropEnts['real_sym;1']!={}):
                    for i in range(len(PropEnts['real_sym;1'])):
                        ient=PropEnts['real_sym;1'][i]
                        nents=len(gmsh.model.getBoundary(1, int(ient)))
                        if(nents!=2):
                            gmsh.logger.write("A 'Real SymAxis Constraint' can only be defined for a Curve of 2 points - not the case for 'Curve "+ient+"'", level="error")
                            return -1
                #
                if(self.nvoids>0):
                    if(PropPgs['void_sym;1']!=[]):
                        gmsh.logger.write("A 'Physical Curve' cannot get a 'Void SymAxis Constraint'", level="error")
                        return -1
                    #
                    if(PropEnts['void_sym;1']!={}):
                        for i in range(len(PropEnts['void_sym;1'])):
                            ient=PropEnts['void_sym;1'][i]
                            nents=len(gmsh.model.getBoundary([(1, int(ient))]))
                            if(nents!=2):
                                gmsh.logger.write("A 'Void SymAxis Constraint' can only be defined for a Curve of 2 points - not the case for 'Curve "+ient+"'", level="error")
                                return -1


            # Verification on entities/physgroups: Test that the TSH geometry has been correctly defined (at this place in the code because it requires the entity node coords)
            temtyp=""

            if(ndims==2):
                tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","key","TEM-TSH")],False)
                temtyp=tmp0["name"]
                istsh=temtyp=="MAKE.TSH"

                if istsh:
                    rc=self.verifyRectangleGeomTSH(PropPgs['mats;'+str(ishptyp)],PropEnts['mats;'+str(ishptyp)])
                if(rc!=0):
                    return rc


            # Verification on global params: Test that user did not select together TSH and TOR
            if(ndims==2 and istorsrun):
                if(temtyp=="MAKE.TSH"):
                    gmsh.logger.write("TSH run cannot support Torsion option", level="error")
                    return -1

        #
        #Retrieve all mesh elements and physical groups
        allNodeTags=[]
        allNodeCoords=[]
        allElemTags=[];allElemTypes=[];allElemEntityTags=[];allElemNodeTags=[]
        #
        for i in range(ndims+1):
            allElemTags.append([])
            allElemTypes.append([])
            allElemEntityTags.append([])
            allElemNodeTags.append([])
        #
        GroupTags={}
        for iprop in propstrs:
            igtypdim=iprop[0]
            igtyp,idim=igtypdim.split(';')
            idim=int(idim)
            GroupTags[igtypdim]={}

        #
        for e in entities:
            # Dimension and tag of the entity
            dim = e[0]
            tag = e[1]

            # Rearrange the entities/elems/nodes/physical groups
            try:
                # Nodes and coords: stored as developed lists
                nodeTags, nodeCoords, nodeParams = gmsh.model.mesh.getNodes(dim, tag)
                allNodeTags+=list(nodeTags)

                allNodeCoords+=list(nodeCoords)
                # Elements of mesh according to the dimension:
                # - elemTypes stored in allElemTypes[dim][...]
                # - elemTags stored in allElemTags[dim][...]
                # - keeping track of the entity tag for each elem tag in allElemEntityTags[dim][...]
                # - elemNodeTags stored in allElemNodeTags[dim][elems...][nodes]

                elemTypes, elemTags, elemNodeTags = gmsh.model.mesh.getElements(dim, tag)

                ntyps=len(elemTypes)
                for ityp in range(ntyps): # elements can be of different types (2D: mix of triangles-quadrangles..., 3D:...)
                    ielemtype=elemTypes[ityp]
                    nnodesperelem=self.allElemTypesNbNodes[ielemtype]
                    nelemtags=len(elemTags[ityp])
                    allElemTags[dim]+=list(elemTags[ityp])
                    allElemTypes[dim]+=[ielemtype for i in range(nelemtags)]
                    allElemEntityTags[dim]+=[tag for i in range(nelemtags)] # recall which entity for each elem, to allocate the materials and constraints
                    tmpelemnodes=[]
                    for i in range(nelemtags):
                        tmpelemnode=[]
                        for j in range(nnodesperelem):
                            tmpelemnode.append(elemNodeTags[ityp][nnodesperelem*i+j])
                        tmpelemnodes.append(tmpelemnode)
                    allElemNodeTags[dim]+=tmpelemnodes

            except Exception as emsg:
                gmsh.logger.write("Pb with mesh Nodes or Elements:"+str(emsg), level="error")
                return -1


            # Store group tag by entity tag, if physgroup is a property physgroup - TBD : verify that "raise Value Error" below is always required in Structural case (maybe not for Global Material)

            try:
                physicalTags = gmsh.model.getPhysicalGroupsForEntity(dim, tag)
                if len(physicalTags):
                    firstMat=True
                    for p in physicalTags:
                        n = gmsh.model.getPhysicalName(dim, p)
                        #print ("name: ",n,p,dim,tag)
                        for iprop in propstrs:
                            igtypdim=iprop[0]
                            igtyp,idim=igtypdim.split(';')
                            idim=int(idim)
                            #
                            if(igtypdim=="beamlax;1"):
                                print('tag,GroupTags[igtypdim]=',tag,GroupTags[igtypdim])

                            if(tag in GroupTags[igtypdim] and str(p) in PropPgs[igtypdim]) and not 'load' in igtypdim and not 'blks' in igtypdim:
                                raise ValueError("Pb with entity "+str(tag)+" being present in more than one "+igtypdim+" group: already in "+str(p))
                            if(str(p) in PropPgs[igtypdim]):
                                if not 'load' in igtypdim and not 'blks' in igtypdim:
                                    GroupTags[igtypdim][tag]=str(p)
                                else: # Special case for loads and blks
                                    if tag in GroupTags[igtypdim]:
                                        GroupTags[igtypdim][tag]+=";"+str(p)
                                    else:
                                        GroupTags[igtypdim][tag]=str(p)

            except Exception as emsg:
                gmsh.logger.write("Pb with properties:"+str(emsg), level="error")
                return -1

#         for iprop in propstrs:
#             igtypdim=iprop[0]
#             print("igtypdim=",igtypdim,":GroupTags=",GroupTags[igtypdim])

        # Number of nodes, elems(ndims), elems(ndims-1)
        nnodes=len(allNodeTags)
        nelems=len(allElemTags[ndims])
        ndimsm=ndims-1
        nelemsm=len(allElemTags[ndimsm])
        nalldims=[k for k in range(ndims+1)]
        nallelems=[len(allElemTags[nalldims[k]]) for k in range(ndims+1)]


        # Verifications for Structural 3D:
        if(not self.isThermal and ndims==3):
            if len(PropEnts['shcormat;2'])>0 or len(PropPgs['shcormat;2'])>0:
                rc=self.verifyQuads(PropEnts['shcormat;2'],PropPgs['shcormat;2'],allElemEntityTags[2],allElemNodeTags[2])
                if(rc!=0):
                    return rc


        #WARNING: allElemTags[0] has very weird values!!! (not linked to the nodes numbering in allElemNodeTags, which has coherent values with Node labels in the GUI) => Caution: use only node numbers from allElemNodeTags, never allElemTags[0]

        # Allocation of ElemVals (single property value allocated to one F.E.)
        # + Verifications on mesh elements :
        # (1) test that all elems have a material allocated,
        # (2) test that a same element is not present in entity and physgroup together
        #
        # Get mesh element physical properties:

        #Verify that some material has been defined
        matsThere=False
        for iprop in propstrs:
            if(not matsThere):
                igtypdim=iprop[0]
                igtyp,idim=igtypdim.split(';')
                if(self.isThermal and ('mats' in igtypdim and PropAtts[igtypdim]!={})):
                    matsThere=True
                elif(not self.isThermal and (('beamcormat' in igtypdim and PropAtts[igtypdim]!={}) or ('trusscormat' in igtypdim and PropAtts[igtypdim]!={})
                    or ('shcormat' in igtypdim and PropAtts[igtypdim]!={}) or ('solcormat' in igtypdim and PropAtts[igtypdim]!={})) ):
                    matsThere=True
        if(not matsThere):
            gmsh.logger.write("No mats defined!", level="error")
            return -1
        #
        try:
            ElemVals={}
            for iprop in propstrs:
                igtypdim=iprop[0]
                igtyp,idim=igtypdim.split(';')
                idim=int(idim)
                kelems=nallelems[idim]
                kdims=nalldims[idim]

                if(igtyp!='real_sym' and igtyp!='void_sym' and igtyp!="trusscormat"):
                    ElemVals[igtypdim]=[]
                    for i in range(kelems):
                        ielem=allElemTags[kdims][i]
                        ientity=allElemEntityTags[kdims][i]
                        #
                        valuestr=""
                        if str(ientity) in PropEnts[igtypdim]:
                            valuestr=PropValEnts[igtypdim][PropEnts[igtypdim].index(str(ientity))]

                            if(igtyp!="same"):
                                ElemVals[igtypdim].append(valuestr)
                            else: # for SAME, aggregate the info on group
                                valuestr+="/e_"+str(idim)+"_"+str(ientity)
                                ElemVals[igtypdim].append(valuestr)
                        #
                        if ientity in GroupTags[igtypdim]:
                            if(len(ElemVals[igtypdim])==i+1 and not 'load' in igtyp and not 'blks' in igtyp):
                                raise ValueError("ielem="+str(ielem)+" has simultaneously a '"+igtypdim+"' property as physgroup '"+str(GroupTags[igtypdim][ientity])+"' and as entity '"+str(ientity)+"'! Need to select only one definition")
                            elif 'load' in igtyp or 'blks' in igtyp:
                                igps=GroupTags[igtypdim][ientity].split(';')
                                for igp in igps:
                                    if(valuestr==""):
                                        valuestr=PropValPgs[igtypdim][PropPgs[igtypdim].index(igp)]
                                    else:
                                        valuestr+=";"+PropValPgs[igtypdim][PropPgs[igtypdim].index(igp)]
                                ElemVals[igtypdim].append(valuestr)
                            else:
                                valuestr=PropValPgs[igtypdim][PropPgs[igtypdim].index(GroupTags[igtypdim][ientity])]
                                if(igtyp!="same"):
                                    ElemVals[igtypdim].append(valuestr)
                                else:
                                    valuestr+="/p_"+str(idim)+"_"+str(GroupTags[igtypdim][ientity])
                                    ElemVals[igtypdim].append(valuestr)

                        #
                        if not (ientity in GroupTags[igtypdim] or str(ientity) in PropEnts[igtypdim]):
                            if(igtyp=='mats'): # Special case for material: every elem needs a material allocated (not the case for Struct, because a 1D object is not necessarily a Beam or Truss
                                raise ValueError("No "+igtyp+" entity or physgroup found for ielem="+str(ielem)+" in entity="+str(ientity)+"!")
                            else:
                                ElemVals[igtypdim].append("-1")
        except Exception as emsg:
            gmsh.logger.write("Pb in allocating property value to elems:"+str(emsg), level="error")
            return -1

#         print("ElemVals[sload;1]=",ElemVals["sload;1"])
#         return -1

        #Special case of TrapezLoad (tgload and tlload) and Relax (beamrelax): add information in ElemVals concerning the individual elems:
        # - trapezload:
        #- relax:
        idim=1
        kelems=nallelems[idim]
        kdims=nalldims[idim]
        nbelems={}
        for i in range(kelems):
            ientity=allElemEntityTags[kdims][i]
            if ientity in nbelems:
                nbelems[ientity]+=1
            else:
                nbelems[ientity]=1

        for igtypdim in ["beamrelax;1","tgload;1","tlload;1"]:
            if igtypdim in ElemVals and ElemVals[igtypdim]!=[]:
                for i in range(kelems):
                    if ElemVals[igtypdim][i]!="-1":
                        ientity=allElemEntityTags[kdims][i]
                        #
                        if (i>0 and allElemEntityTags[kdims][i-1]!=ientity) or i==0: # identifies the first left elem of the Beam
                            ElemVals[igtypdim][i]+="/L"
                            ielem_idx=0
                        elif (i<kelems-1 and allElemEntityTags[kdims][i+1]!=ientity) or i==kelems-1: # identifies the last right elem of the Beam
                            ElemVals[igtypdim][i]+="/R"
                            ielem_idx+=1
                        else: # intermediate elems in the Beam
                            ElemVals[igtypdim][i]+="/I"
                            ielem_idx+=1
                        #
                        if not igtypdim=="beamrelax;1":
                            ElemVals[igtypdim][i]+=";"+str(ielem_idx)+";"+str(nbelems[ientity])
                        #



        # (Thermal 2D TSH): Verification on meshnodes
        if istsh:
           rc= self.verifMeshTSH(PropPgs['mats;'+str(ishptyp)],PropEnts['mats;'+str(ishptyp)],allElemEntityTags[1])
           if(rc!=0):
                return rc


        # (Structural): get the NDOFMAX - FEM considered are those with some Mats defined
        if not self.isThermal:
            if(ndims==2):
                if("trusscormat;1" in ElemVals):
                    if([k for k in ElemVals["trusscormat;1"] if k!="-1"]!=[]):
                        ndofmax=2
                if("beamcormat;1" in ElemVals):
                    if([k for k in ElemVals["beamcormat;1"] if k!="-1"]!=[]):
                        ndofmax=3
            else: #ndim=3
                if(PropPgs["trusscormat;1"]!=[] or PropEnts["trusscormat;1"]!=[]):
                        ndofmax=3
                if("solcormat;3" in ElemVals):
                    if([k for k in ElemVals["solcormat;3"] if k!="-1"]!=[]):
                        ndofmax=3
                if("shcormat;2" in ElemVals):
                    if([k for k in ElemVals["shcormat;2"] if k!="-1"]!=[]):
                        ndofmax=6
                if("beamcormat;1" in ElemVals):
                    if([k for k in ElemVals["beamcormat;1"] if k!="-1"]!=[]):
                        ndofmax=7
        else:
            ndofmax=1
            print('ndofmax=',ndofmax)

        # SAME (Thermal and Structural): Agregate from ElemVals to NodeVals - Verfication: Detect if contradictory constraint has been assigned to nodes
        SameNodeVals={}
        for iprop in propstrs:
            igtypdim=iprop[0]
            igtyp,idim=igtypdim.split(';')

            if(igtyp=="same"):
                idim=int(idim)
                kelems=nallelems[idim]
                kdims=nalldims[idim]
                if PropAtts[igtypdim]!={}:
                    for i in range(kelems):
                        ival=ElemVals[igtypdim][i]
                        if(ival!="-1"):
                            ivalpart1=ival.split("/")[0]
                            ivalpart2=ival.split("/")[1]
                            ityp=allElemTypes[kdims][i]
                            inodesperelem=self.allElemTypesNbNodes[ityp]
                            for icoord in range(inodesperelem):
                                inode=allNodeTags.index(allElemNodeTags[kdims][i][icoord])+1
                                #inode=allElemNodeTags[kdims][i][icoord]
                                if(inode in SameNodeVals):
                                    svalpart1=SameNodeVals[inode].split("/")[0]
                                    svalpart2=SameNodeVals[inode].split("/")[1]
                                    svaltab=svalpart2.split(";")
                                    if(ivalpart1!=svalpart1):
                                        gmsh.logger.write("Error: Node has already been assigned with '"+svalpart1+"' from '"+svalpart2+"', now trying to assign contradictory '"+ivalpart1+"' from '"+ivalpart2+"'", level="error")
                                        return -1
                                    else:
                                        if(not ivalpart2 in svaltab):
                                            SameNodeVals[inode]=SameNodeVals[inode]+";"+ivalpart2

                                else:
                                    SameNodeVals[inode]=ival
        #
        samevals={}
        snodes=list(SameNodeVals.keys())
        svals=list(SameNodeVals.values())
        svalmerged=self.mergeSameIdx(svals)
        #
        for i in range(len(svalmerged)):
            ival=svalmerged[i]
            inode=snodes[i]
            if(ival in samevals):
                samevals[ival].append(inode)
            else:
                samevals[ival]=[inode]
        #
        # Prepare SAME to write (Thermal and Structural)
        SAMEnodes=[]
        for ival in samevals:
            ivaltab=ival.split("/")[0].split(' - ')

            for i in range(1,len(samevals[ival])):
                tmp={}
                tmp['val']=['SAME',samevals[ival][i],samevals[ival][0]]+ivaltab[0:ndofmax]
                tmp['fmt']='(A10,I6,I6'
                for i0 in range(ndofmax):
                    tmp['fmt']+=',A10'
                tmp['fmt']+=")"
                SAMEnodes.append(tmp)

        # (Thermal) : Special storage for 'real_sym' and 'void_sym', where a same point(=elem) can belong to multiple symAxis
        # len(gmsh.model.mesh.getNodes(0, int(ient)))
        if(self.isThermal):
            if(ndims==2):
                syms={}
                symvals={}
                for igtypdim in ['real_sym;1','void_sym;1']:
                    syms[igtypdim]={}
                    symvals[igtypdim]={}
                    kdims=1
                    if(self.nvoids>0):
                        if(PropEnts[igtypdim]!={}):
                            for i in range(len(PropEnts[igtypdim])):
                                ikey=i
                                val=PropValEnts[igtypdim][i]
                                ient=PropEnts[igtypdim][i]
                                inodes=gmsh.model.getBoundary([(1, int(ient))])
                                for itup in inodes:
                                    inode,_,_=gmsh.model.mesh.getNodes(0,itup[1])
                                    inode_safir=allNodeTags.index(inode[0])+1
                                    if(not ikey in syms[igtypdim]):
                                        syms[igtypdim][ikey]=[inode_safir]
                                    else:
                                        syms[igtypdim][ikey].append(inode_safir)
                                symvals[igtypdim][ikey]=val
                print("syms=",syms['void_sym;1'])
        #


        # Prepare Nodes to write (Thermal and Structural)
        INnodes=[]
        # Node Nubmering is very specific for TSH calculation:
        if istsh:
            rc,correspnodes=self.specialNodeNumberingTSH(PropPgs['mats;'+str(ishptyp)],PropEnts['mats;'+str(ishptyp)],allElemEntityTags[1],allElemNodeTags[1],allNodeTags,allNodeCoords)
            nnodes=len(correspnodes)
            if(rc==-1):
                return -1 # Message has already been displayed in subroutine
            #
        for i in range(nnodes):
                idx=i+1 # Redefine the node indexes in the outfile
                if istsh:
                    icor=correspnodes[i]
                else:
                    icor=i
                tmp={}
                if(ndims==2 and self.isThermal):
                    tmp['val']=['NODE',idx,allNodeCoords[3*icor+1],allNodeCoords[3*icor]]  # Reverse because SAFIR X-coord is GMSH Y-coord, and SAFIR Y-coord is GMSH X-coord
                    tmp['fmt']='(A10,I6,F11.4,F11.4)'
                elif(ndims==2):
                    tmp['val']=['NODE',idx,allNodeCoords[3*icor],allNodeCoords[3*icor+1]]  # Reverse because SAFIR X-coord is GMSH Y-coord, and SAFIR Y-coord is GMSH X-coord
                    tmp['fmt']='(A10,I6,F11.4,F11.4)'
                elif(ndims==3):
                    tmp['val']=['NODE',idx,allNodeCoords[3*icor],allNodeCoords[3*icor+1],allNodeCoords[3*icor+2]]
                    tmp['fmt']='(A10,I6,F11.4,F11.4,F11.4)'
                INnodes.append(tmp)


        # 2/ Prepare imposed temperatures for writing (separately Thermal and Structural)
        INfixnodes=[]

        if(self.isThermal): #(Thermal)
            fixnodes={}
            try:
                for iprop in propstrs:
                    igtypdim=iprop[0]
                    if('blks' in igtypdim or ('tors' in igtypdim and istorsrun)):
                        igtyp,idim=igtypdim.split(';')
                        idim=int(idim)
                        kelems=nallelems[idim]
                        kdims=nalldims[idim]
                        if PropAtts[igtypdim]!={}:
                            #
                            for i in range(kelems):
                                ielem=allElemTags[kdims][i]
                                ival=ElemVals[igtypdim][i]
                                #
                                if(ival!="-1"):
                                    tmp={}
                                    inodesperelem=self.allElemTypesNbNodes[allElemTypes[kdims][i]]
                                    #
                                    for icoord in range(inodesperelem):
                                        #print
                                        inode=allNodeTags.index(allElemNodeTags[kdims][i][icoord])
                                        if istsh:
                                            inode_safir=correspnodes.index(inode)+1
                                        else:
                                            inode_safir=inode+1
                                        #
                                        #if(inode_safir in fixnodes):
                                        #    if(ival!=fixnodes[inode_safir]):
                                        #        raise ValueError("Node "+str(inode_safir)+" has already been assigned a different value: "+fixnodes[inode_safir])
                                        #else:
                                        #    fixnodes[inode_safir]=ival

                                        #TBCkecked if needs to be inside or outside the icoord-loop above
                                        #ival0=fixnodes[inode_safir]

                                        for ijval in ival.split(";"):
                                            tmp['val']=['BLOCK',inode_safir,ijval]
                                            tmp['fmt']='(A10,I6,A15)'
                                            INfixnodes.append(tmp)

            except Exception as emsg:
                gmsh.logger.write("Pb in getting fixations by node:"+str(emsg), level="error")
                return -1

        else: # (Structural)
        # BLOCKS : Agregate from ElemVals to fixnodes - Verfication: Detect if contradictory constraint has been assigned to nodes
            fixnodes={}
            for iprop in propstrs:
                igtypdim=iprop[0]
                igtyp,idim=igtypdim.split(';')

                if(igtyp=="blks"):
                    idim=int(idim)
                    kelems=nallelems[idim]
                    kdims=nalldims[idim]
                    #if():

                    if PropAtts[igtypdim]!={}:
                        for i in range(kelems):
                            ival=ElemVals[igtypdim][i]
                            if(ival!="-1"):
                                ityp=allElemTypes[kdims][i]
                                inodesperelem=self.allElemTypesNbNodes[ityp]
                                for icoord in range(inodesperelem):
                                    inode=allNodeTags.index(allElemNodeTags[kdims][i][icoord])+1
                                    #inode=allElemNodeTags[kdims][i][icoord]
                                    #if(inode in fixnodes):
                                    #    ival0=fixnodes[inode]
                                    #    if(ival!=ival0):
                                    #        gmsh.logger.write("Error: Node has already been assigned with '"+ival0+"', now trying to assign contradictory '"+ival+"'", level="error")
                                    #        return -1
                                    #else:
                                    #    fixnodes[inode]=ival
        #
            #for inode,ival in fixnodes.items():
                                    for ijval in ival.split(";"):
                                        ivaltab=ijval.split("/")[0].split(' - ')
                                        tmp={}
                                        tmp['val']=['BLOCK',inode]+ivaltab[0:ndofmax]
                                        tmp['fmt']='(A10,I6,'
                                        for i0 in range(ndofmax):
                                            tmp['fmt']+=',A15'
                                        tmp['fmt']+=")"
                                        INfixnodes.append(tmp)


        # 4/ Prepare F.E. for writing (separately Thermal nd Structural)
        if(self.isThermal): # (Thermal)
            INelems=[]
            try:
                if(ndims==2):
                    nnodesperelemmax=4
                if(ndims==3):
                    nnodesperelemmax=8
                for i in range(nelems):
                    tmp={}
                    ielem=allElemTags[ndims][i]
                    ientity=allElemEntityTags[ndims][i]
                    imat=ElemVals['mats;'+str(ishptyp)][i]
                    inodesperelem=self.allElemTypesNbNodes[allElemTypes[ndims][i]]
                    ncoords=[] #number of nodes for the elems, completed for SAFIR to 4 (dim=2) or to 8 (dim=3)
                    for icoord in range(inodesperelem):
                        inode=allNodeTags.index(allElemNodeTags[ndims][i][icoord])
                        if istsh:
                            inode_safir=correspnodes.index(inode)
                        else:
                            inode_safir=inode
                        ncoords.append(inode_safir+1)

                    if(inodesperelem<nnodesperelemmax):
                        for icoord in range(nnodesperelemmax-inodesperelem):
                            ncoords.append(0)

                    ffmt="(A10,I8,"
                    idx=i+1  # Redefine the elem indexes in the outfile
                    flst=[];flst.append('ELEM');flst.append(idx); # write the elem index in the outfile, not the elemtag
                    for icoord in range(nnodesperelemmax):
                        ffmt+="I6,"
                        flst.append(ncoords[icoord])
                    #ffmt+="I8,F7.0)"
                    ffmt+="I8,I7)"
                    flst.append(imat);flst.append(0.)
                    tmp['val']=flst
                    tmp['fmt']=ffmt
                    INelems.append(tmp)

            except Exception as emsg:
                gmsh.logger.write("Pb for preparing F.E. for writing:"+str(emsg), level="error")
                return -1
        #
        else: #Structural: Only Beams, Shells and Truss for now - TBD: extend to Spring, Solid
            #
            #  Prepare Beams for writing (Structural)
            idxelem=0
            idxbeams=[]
            INelemBeams=[]
            INsectionBeams=[]
            NFIBER=1
            #
            try:
                if(ndims==2):
                    nnodesperelemmax=3
                if(ndims==3):
                    nnodesperelemmax=4
                #
                idx=nnodes;idxelem=0
                igtypdim='beamcormat;1'
                igtypdim2='beamlax;1'
                ientityold=-999

                if PropAtts[igtypdim]!={}:
                    for i in range(nallelems[1]):
                        if(ElemVals[igtypdim][i]!="-1"):
                            tmp={};tmpelem={}

                            ielem=allElemTags[1][i]
                            ientity=allElemEntityTags[1][i]

                            if(ndims==3 and ElemVals[igtypdim2][i]=="-1"):
                                raise ValueError(" Need to assign a local axes to 'Curve "+str(ientity)+"'")
                            #
                            inodesperelem=self.allElemTypesNbNodes[allElemTypes[1][i]]
                            idx1=allNodeTags.index(allElemNodeTags[1][i][0])
                            idx2=allNodeTags.index(allElemNodeTags[1][i][1])
                            node1=idx1+1 # left point of Beam
                            node2=idx2+1 # rightpoint of Beam
                            #
                            # Add 3rd (middle node)
                            idx+=1
                            node3=idx
                            if(ndims==2 and self.isThermal):
                                x1=allNodeCoords[3*idx1+1];y1=allNodeCoords[3*idx1]
                                x2=allNodeCoords[3*idx2+1];y2=allNodeCoords[3*idx2]
                                x3=(x1+x2)/2;y3=(y1+y2)/2;z3=0
                                tmp['val']=['NODE',idx,x3,y3]
                                tmp['fmt']='(A10,I6,F11.4,F11.4)'

                            elif(ndims==2):
                                x1=allNodeCoords[3*idx1];y1=allNodeCoords[3*idx1+1]
                                x2=allNodeCoords[3*idx2];y2=allNodeCoords[3*idx2+1]
                                x3=(x1+x2)/2;y3=(y1+y2)/2;z3=0
                                tmp['val']=['NODE',idx,x3,y3]
                                tmp['fmt']='(A10,I6,F11.4,F11.4)'
                            #
                            elif(ndims==3):
                                x1=allNodeCoords[3*idx1];y1=allNodeCoords[3*idx1+1];z1=allNodeCoords[3*idx1+2]
                                x2=allNodeCoords[3*idx2];y2=allNodeCoords[3*idx2+1];z2=allNodeCoords[3*idx2+2]
                                x3=(x1+x2)/2;y3=(y1+y2)/2;z3=(z1+z2)/2
                                tmp['val']=['NODE',idx,x3,y3,z3]
                                tmp['fmt']='(A10,I6,F11.4,F11.4,F11.4)'
                            #
                            INnodes.append(tmp)
                            #
                            # Store different sections:
                            imat=ElemVals[igtypdim][i]
                            if(imat in INsectionBeams):
                                sectidx=INsectionBeams.index(imat)+1
                            else:
                                INsectionBeams.append(imat)
                                sectidx=len(INsectionBeams)
                            #
                            # Struct 3D Only: Add 4th node (longer axis of the beam slice)
                            #
                            if(ndims==3):
                                if(ientity!=ientityold):
                                    ilax=ElemVals[igtypdim2][i]
                                    idx+=1
                                    node4=idx
                                    #
                                    self.laxid=[k for k in range(len(self.listLAX)) if ilax+";1" in list(self.listLAX[k].keys())[0]][0]
                                    #self.isViewLAX=False
                                    self.LAXspecial=True
                                    (Yp_x,Yp_y,Yp_z)=self.recreateLAXView("Curve "+str(ientity))
                                    x4=x3+Yp_x;y4=y3+Yp_y;z4=z3+Yp_z
                                    self.LAXspecial=False
                                    ientityold=ientity
                                    tmp={}
                                    tmp['val']=['NODE',idx,x4,y4,z4]
                                    tmp['fmt']='(A10,I6,F11.4,F11.4,F11.4)'
                                    INnodes.append(tmp)

                            # Add NODOFBEAM
                            idxbeams.append(ielem)
                            idxelem+=1
                            if(ndims==2):
                                tmpelem['val']=['ELEM',idxelem,node1,node3,node2,sectidx]
                                tmpelem['fmt']='(A10,I6,I11,I11,I11,I11)'
                            if(ndims==3):
                                tmpelem['val']=['ELEM',idxelem,node1,node3,node2,node4,sectidx]
                                tmpelem['fmt']='(A10,I6,I11,I11,I11,I11,I11)'
                            #
                            INelemBeams.append(tmpelem)
                #
                # Get NFIBER
                for i in range(len(INsectionBeams)):
                    imat=INsectionBeams[i]
                    ifile=imat.split(' - ')[0].strip()
                    try:
                        file0=os.path.join(self.dir,ifile)
                        f=open(file0,'r')
                        lines=f.readlines()
                        iline=[k for k in lines if 'NFIBERBEAM' in k][0]
                        NFIB=int(iline.split('NFIBERBEAM')[1].replace("\r","").replace("\n",""))
                        NFIBER=max(NFIBER,NFIB)
                        f.close()
                    except Exception as emsg0:
                        gmsh.logger.write("Pb in reading file "+file0+": "+str(emsg0)+" - will keep precedent determined value", level="warning")
                        #
            except Exception as emsg:
                gmsh.logger.write("Pb in preparing Beam elems for writing:"+str(emsg), level="error")
                return -1

            NBEAM=idxelem
            NGEOBEAM=len(INsectionBeams)

            #
            # Prepare Shell for writing (Structural)
            INelemShells=[]
            NREBARS=0
            idxshells=[]
            INsectionShells=[]
            idxelem=0
            #
            try:
                nnodesperelemmax=4
                #
                igtypdim='shcormat;2'
                igtypdim2='rebar;2'

                ientityold=-999

                if igtypdim in PropAtts and PropAtts[igtypdim]!={}:
                    for i in range(nallelems[2]):
                        if(ElemVals[igtypdim][i]!="-1"):
                            tmp={};tmpelem={}
                            ielem=allElemTags[2][i]
                            ientity=allElemEntityTags[2][i]
                            #
                            inodesperelem=self.allElemTypesNbNodes[allElemTypes[2][i]]
                            idx1=allNodeTags.index(allElemNodeTags[2][i][0])
                            idx2=allNodeTags.index(allElemNodeTags[2][i][1])
                            idx3=allNodeTags.index(allElemNodeTags[2][i][2])
                            idx4=allNodeTags.index(allElemNodeTags[2][i][3])
                            #
                            node1=idx1+1
                            node2=idx2+1
                            node3=idx3+1
                            node4=idx4+1
                            #
                            # Store different sections:
                            imat=ElemVals[igtypdim][i]
                            irebar=ElemVals[igtypdim2][i]
                            if(irebar!="-1"):
                                nbar=int(irebar.split("/")[0])
                                NREBARS=max(NREBARS,nbar)
                            ikey=imat+"//"+irebar
                            if(ikey in INsectionShells):
                                sectidx=INsectionShells.index(ikey)+1
                            else:
                                INsectionShells.append(ikey)
                                sectidx=len(INsectionShells)

                            # Add NODOFSHELL
                            idxshells.append(ielem)
                            idxelem+=1
                            tmpelem['val']=['ELEM',idxelem,node1,node2,node3,node4,sectidx]
                            tmpelem['fmt']='(A10,I6,I11,I11,I11,I11,I11)'
                            #
                            INelemShells.append(tmpelem)
                        #
            except Exception as emsg:
                gmsh.logger.write("Pb in preparing Shell elems for writing (Did you Recombine to get only quads before meshing?):"+str(emsg), level="error")
                return -1

            NSHELL=idxelem
            #NGEOSHELL=len(INelemShells)
            NGEOSHELL=len(INsectionShells)

            #
            # Prepare Truss for writing (Structural): FE is the entire Curve (mesh=2 extrem points)
            INelemTruss=[]
            INgroupTruss=[]
            idxelem=0
            #
            for i in range(len(PropPgs['trusscormat;1'])):
                ipg=int(PropPgs['trusscormat;1'][i])
                for ient in gmsh.model.getEntitiesForPhysicalGroup(1, int(ipg)):
                    tmpelem={}
                    shpedges=gmsh.model.getBoundary([(1, int(ient))],recursive=True)
                    node1=allNodeTags.index([allElemNodeTags[0][i0] for i0 in range(nallelems[0]) if allElemEntityTags[0][i0]==shpedges[0][1]][0][0])+1
                    node2=allNodeTags.index([allElemNodeTags[0][i0] for i0 in range(nallelems[0]) if allElemEntityTags[0][i0]==shpedges[1][1]][0][0])+1
                    #
                    # Store different sections:
                    imat=PropValPgs['trusscormat;1'][i]
                    if(imat in INgroupTruss):
                        sectidx=INgroupTruss.index(imat)+1
                    else:
                        INgroupTruss.append(imat)
                        sectidx=len(INgroupTruss)
                    #
                    # Add NODOFTRUSS
                    idxelem+=1
                    tmpelem['val']=['ELEM',idxelem,node1,node2,sectidx]
                    tmpelem['fmt']='(A10,I6,I11,I11,I11)'
                    #
                    INelemTruss.append(tmpelem)
            #
            for i in range(len(PropEnts['trusscormat;1'])):
                ient=int(PropEnts['trusscormat;1'][i])
                tmpelem={}
                shpedges=gmsh.model.getBoundary([(1, int(ient))],recursive=True)
                node1=allNodeTags.index([allElemNodeTags[0][i0] for i0 in range(nallelems[0]) if allElemEntityTags[0][i0]==shpedges[0][1]][0][0])+1
                node2=allNodeTags.index([allElemNodeTags[0][i0] for i0 in range(nallelems[0]) if allElemEntityTags[0][i0]==shpedges[1][1]][0][0])+1
                #
                # Store different sections:
                imat=PropValEnts['trusscormat;1'][i]
                if(imat in INgroupTruss):
                    sectidx=INgroupTruss.index(imat)+1
                else:
                    INgroupTruss.append(imat)
                    sectidx=len(INgroupTruss)
                #
                # Add NODOFTRUSS
                idxelem+=1
                tmpelem['val']=['ELEM',idxelem,node1,node2,sectidx]
                tmpelem['fmt']='(A10,I6,I11,I11,I11)'
                #
                INelemTruss.append(tmpelem)
            #
            NTRUSS=idxelem
            NGEOTRUSS=len(INgroupTruss)


            #
            # Prepare Solid for writing (Structural)
            INelemSolid=[]
            idxelem=0
            NSOLID=0

            #
            try:
                nnodesperelemmax=8
                #
                idxelem=0
                igtypdim='solcormat;3'
                ientityold=-999

                if igtypdim in PropAtts and PropAtts[igtypdim]!={}:
                    for i in range(nallelems[3]):
                        if(ElemVals[igtypdim][i]!="-1"):
                            tmp={};tmpelem={}
                            ielem=allElemTags[3][i]
                            ientity=allElemEntityTags[3][i]
                            #
                            inodesperelem=self.allElemTypesNbNodes[allElemTypes[3][i]]
                            ncoords=[] #number of nodes for the elems
                            for icoord in range(inodesperelem):
                                ncoords.append(allNodeTags.index(allElemNodeTags[3][i][icoord])+1) # node numbering in SAFIR
                                #ncoords.append(allElemNodeTags[3][i][icoord]) # DEBUG: node numbering in GMSH
                            if(inodesperelem<nnodesperelemmax):
                                for icoord in range(nnodesperelemmax-inodesperelem):
                                    ncoords.append(0)
                            #
                            # Add NODOFSOLID

                            idxelem+=1
                            _,imat,res1,res2,res3=ElemVals[igtypdim][i].split(' - ')
                            iglomat=[i0 for i0 in range(len(self.listMats)) if list(self.listMats[i0].keys())[0].split('/')[0]==imat+";3"][0]
                            res1=float(res1);res2=float(res2);res3=float(res3)
                            #
                            tmpelem={}
                            tmpelem['val']=['ELEM',idxelem]
                            tmpelem['fmt']='(A10,I6,'
                            #
                            for icoord in range(nnodesperelemmax):
                                tmpelem['fmt']+=',F10.1'
                                tmpelem['val'].append(float(ncoords[icoord]))
                            tmpelem['fmt']+=',I6'
                            tmpelem['val'].append(iglomat+1)
                            tmpelem['fmt']+=',F10.1,F10.1,F10.1'
                            tmpelem['val'].append(res1);tmpelem['val'].append(res2);tmpelem['val'].append(res3)
                            tmpelem['fmt']+=")"
                            INelemSolid.append(tmpelem)

                        #
            except Exception as emsg:
                gmsh.logger.write("Pb in preparing Solid elems for writing:"+str(emsg), level="error")
                return -1

            NSOLID=idxelem


        # 5/  Prepare  Frontiers for writing (Thermal): Scan for each elems its (ndims-1) component elems, identify if these (ndims-1) elems are part of a (ndims) entity having a frontier defined, if yes write down the nodes sharing the frontier
        if(self.isThermal):
            try:
                #
                if(ndims==2):
                    nfacesperelemmax=4
                if(ndims==3):
                    nfacesperelemmax=6
                #
                INfrontiers=[]
                for iprop in propstrs:
                    igtypdim=iprop[0]
                    if('flxs' in igtypdim or 'frtiers' in igtypdim):
                        igtyp,idim=igtypdim.split(';')
                        idim=int(idim)
                        kelems=nallelems[idim]
                        kdims=nalldims[idim]

                        if PropAtts[igtypdim]!={}:
                            #
                            if('flxs' in igtypdim):
                                ipref='FLUX'
                            else:
                                ipref='F'
                            #
                            for i in range(nelemsm):
                                if(ElemVals[igtypdim][i]!="-1"):
                                    ielem=allElemTags[ndimsm][i]
                                    ientity=allElemEntityTags[ndimsm][i]

                                    frtierface=allElemNodeTags[ndimsm][i]
                                    frtierface.sort()
                                    found=False
                                    im=0
                                    faceConstraints=['NO' for i0 in range(nfacesperelemmax)]
                                    while(not found and im<nelems):
                                        ielemnodes=allElemNodeTags[ndims][im]
                                        ielemtype=allElemTypes[ndims][im]
                                        idx=im+1 # get the elem index, not the tag, to write in the outfile
                                        ifaces=self.getOrderedFaces(ielemtype,ielemnodes)
                                        for ifa in range(len(ifaces)):
                                            elemface=ifaces[ifa]
                                            elemface.sort()
                                            if(frtierface==elemface):
                                                found=True
                                                ifa0=ifa

                                        if(not found):
                                                im+=1
                            #            print 'im=',im,', / nelems=',nelems,found
                                    if(found):
                            #            print 'nodes:',ielemnodes
                            #            print 'ielemtype: ',ielemtype
                            #            print 'faces:',ifaces
                            #            print 'ifa=',ifa0
                                        tmp={}
                                        faceConstraints[ifa0]=ElemVals[igtypdim][i]
                                        strtmp=""
                                        for it in range(nfacesperelemmax-1):
                                            strtmp+="A12,"
                                        ffmt='(A5,I6,'+strtmp+'A12)'
                                        flst=[ipref,idx]+faceConstraints
                                        tmp['val']=flst
                                        tmp['fmt']=ffmt
                                        INfrontiers.append(tmp)

            except Exception as emsg:
                gmsh.logger.write("Pb in preparing constraints flxs,frtiers for writing:"+str(emsg), level="error")
                return -1


        # 6/ Prepare Voids for writing (Thermal)
        if(self.isThermal):
            if(ndims==2 and self.nvoids>0):
                nfrontiervoids=0
                INvoids={}
                frtvoids={}
                try:
                    #
                    igtypdim='void;1'
                    igtyp='void'
                    ipref='ELEM'
                    if PropAtts[igtypdim]!={}:
                        for i in range(nelemsm):
                            if(ElemVals[igtypdim][i]!="-1"):
                                ival0=ElemVals[igtypdim][i]
                                ielem=allElemTags[ndimsm][i]
                                ientity=allElemEntityTags[ndimsm][i]

                                frtierface=allElemNodeTags[ndimsm][i]
                                frtierface.sort()
                                found=False
                                im=0
                                while(not found and im<nelems):
                                    ielemnodes=allElemNodeTags[ndims][im]
                                    ielemtype=allElemTypes[ndims][im]
                                    idx=im+1 # get the elem index, not the tag, to write in the outfile
                                    ifaces=self.getOrderedFaces(ielemtype,ielemnodes)

                                    for ifa in range(len(ifaces)):
                                        elemface=ifaces[ifa]
                                        elemface.sort()
                                        if(frtierface==elemface):
                                            found=True
                                            ifa0=ifa

                                    if(not found):
                                            im+=1
                                if(found):
                                    tmp={}
                                    tmp['val']=[ipref,idx,ifa0+1]
                                    tmp['fmt']='(A5,I6,I4)'
                                    if(ival0 in INvoids):
                                        INvoids[ival0].append(tmp)
                                        frtvoids[ival0]+=1
                                    else:
                                        INvoids[ival0]=[tmp]
                                        frtvoids[ival0]=1

                        for k,ifrtvoid in frtvoids.items():
                            nfrontiervoids=max(nfrontiervoids,ifrtvoid)

                except Exception as emsg:
                    gmsh.logger.write("Pb in preparing Void for writing "+str(ivoid)+":"+str(emsg), level="error")
                    return -1


        #7/ Prepare Mass for writing (Structural)
        if(not self.isThermal):
            INelemMass=[]
            #
            try:
                for iprop in propstrs:
                    igtypdim=iprop[0]
                    igtyp,idim=igtypdim.split(';')
                    idim=int(idim)
                    if igtyp=="mass":
                        kelems=nallelems[idim]
                        kdims=nalldims[idim]
                        if PropAtts[igtypdim]!={}:
                            #
                            for i in range(kelems):
                                ielem=allElemTags[kdims][i]
                                #
                                if(ElemVals[igtypdim][i]!="-1"):
                                    if(idim==0):
                                        inodetag=allElemNodeTags[kdims][i][0]
                                        idx=allNodeTags.index(inodetag)+1
                                        iflag="M_NODE"
                                    elif(idim==1):
                                        idx=idxbeams.index(ielem)+1
                                        iflag="M_BEAM"
                                    elif(idim==2):
                                        idx=idxshells.index(ielem)+1
                                        iflag="M_SHELL"
                                    #
                                    ivaltab=ElemVals[igtypdim][i].split(' - ')
                                    nparams=len(ivaltab)
                                    tmpelem={}
                                    tmpelem['val']=[iflag,idx]
                                    tmpelem['fmt']='(A10,I6'
                                    for iparam in range(nparams):
                                        tmpelem['fmt']+=',F10.1'
                                        tmpelem['val'].append(float(ivaltab[iparam]))
                                    tmpelem['fmt']+=")"
                                    INelemMass.append(tmpelem)
                            #
            except Exception as emsg:
                gmsh.logger.write("Pb in preparing Mass for writing (Did you define Material for your F.E before meshing?):"+str(emsg), level="error")
                return -1

        #7/ Prepare Loads for writing (Structural)
        if(not self.isThermal):
            INelemLoads={}
            #
            try:
                for iprop in propstrs:
                    igtypdim=iprop[0]
                    igtyp,idim=igtypdim.split(';')
                    idim=int(idim)
                    if 'load' in igtyp:
                        kelems=nallelems[idim]
                        kdims=nalldims[idim]
                        if PropAtts[igtypdim]!={}:
                            #
                            for i in range(kelems):
                                ielem=allElemTags[kdims][i]
                                #
                                if(ElemVals[igtypdim][i]!="-1"):
                                    if(igtyp=="tlload" or igtyp=="tgload"):
                                        ivaltab1,ivalcompl=ElemVals[igtypdim][i].split('/')
                                    else:
                                        ivaltab1=ElemVals[igtypdim][i]
                                    for ivaltab0 in ivaltab1.split(";"):
                                        ivaltab=ivaltab0.split(' - ')
                                        ifunc=ivaltab[0]
                                        nparams=len(ivaltab[1:])
                                        #
                                        if(not ifunc in INelemLoads):
                                            INelemLoads[ifunc]=[]
                                        #
                                        # Recalculate values for special case of trapezoidal loads:
                                        if(igtyp=="tlload" or igtyp=="tgload"):
                                            ivaltab1=copy(ivaltab)
                                            _,inb,nnb=ivalcompl.split(";")
                                            inb=int(inb);nnb=int(nnb)
                                            noffset=int(nparams/2)
                                            for iparam in range(noffset):
                                                ivaltab[1+iparam]=str(float(ivaltab1[1+iparam])+float(inb)/float(nnb)*(float(ivaltab1[1+iparam+noffset])-float(ivaltab1[1+iparam])))
                                                ivaltab[1+iparam+noffset]=str(float(ivaltab1[1+iparam])+float(inb+1)/float(nnb)*(float(ivaltab1[1+iparam+noffset])-float(ivaltab1[1+iparam])))
                                        #
                                        if(idim==0):
                                            inodetag=allElemNodeTags[kdims][i][0]
                                            idx=allNodeTags.index(inodetag)+1
                                            iflag="NODELOAD"
                                        elif(idim==1):
                                            idx=idxbeams.index(ielem)+1
                                            if igtyp=="sload":
                                                iflag="DISTRBEAM"
                                            elif igtyp=="tgload":
                                                iflag="TRAPGLOBM"
                                            elif igtyp=="tlload":
                                                iflag="TRAPLOCBM"
                                        elif(idim==2):
                                            idx=idxshells.index(ielem)+1
                                            iflag="DISTRSH"
                                        #
                                        tmpelem={}
                                        tmpelem['val']=[iflag,idx]
                                        tmpelem['fmt']='(A10,I6'
                                        for iparam in range(nparams):
                                            tmpelem['fmt']+=',F10.2'
                                            tmpelem['val'].append(float(ivaltab[iparam+1]))
                                        tmpelem['fmt']+=")"
                                        INelemLoads[ifunc].append(tmpelem)
                            #
            except Exception as emsg:
                gmsh.logger.write("Pb in preparing Loads for writing (Did you define Material for your F.E before meshing?):"+str(emsg), level="error")
                return -1
            NLOAD=len(INelemLoads)


        #7/ Prepare Beam Relaxtion for writing (Structural)
        if(not self.isThermal):
            INelemRelax=[]
            #
            try:
                #
                if(ndims==2):
                    ndofperelem=6
                if(ndims==3):
                    ndofperelem=14
                #:
                igtypdim='beamrelax;1'
                igtyp,idim=igtypdim.split(';')
                idim=int(idim)
                kelems=nallelems[idim]
                kdims=nalldims[idim]
                if PropAtts[igtypdim]!={}:
                    #
                    for i in range(kelems):
                        if(ElemVals[igtypdim][i]!="-1"):
                            ielem=allElemTags[kdims][i]
                            idx=idxbeams.index(ielem)+1
                            ivaltab0,ivalcompl=ElemVals[igtypdim][i].split('/')
                            ivaltab=ivaltab0.split(' - ')
                            #
                            if ivalcompl=="L" or ivalcompl=="R":
                                tmpelem={}
                                tmpelem['val']=['ELEM',idx]
                                tmpelem['fmt']='(A10,I6'
                                #
                                if(ivalcompl=="L"):
                                    noffset=0
                                if(ivalcompl=="R"):
                                    noffset=int(ndofperelem/2)
                                #
                                if(ivalcompl=="R"):
                                    for idof in range(int(ndofperelem/2)):
                                        tmpelem['fmt']+=',F10.1'
                                        tmpelem['val'].append(-1.0)
                                #
                                for idof in range(int(ndofperelem/2)):
                                    tmpelem['fmt']+=',F10.1'
                                    tmpelem['val'].append(float(ivaltab[idof+noffset]))
                                #
                                if(ivalcompl=="L"):
                                    for idof in range(int(ndofperelem/2)):
                                        tmpelem['fmt']+=',F10.1'
                                        tmpelem['val'].append(-1.0)
                                tmpelem['fmt']+=")"
                                INelemRelax.append(tmpelem)
                        #

            except Exception as emsg:
                gmsh.logger.write("Pb in preparing Beam Relaxations for writing:"+str(emsg), level="error")
                return -1

            print('INelemRelax=',INelemRelax)

        #7/ Prepare Hydrostat Beam Loads for writing (Structural)
        if(not self.isThermal):
            INelemHydrost={}
            NHYDROST=0
            #
            try:
                #:
                igtypdim='hydrostat;1'
                igtyp,idim=igtypdim.split(';')
                idim=int(idim)
                kelems=nallelems[idim]
                kdims=nalldims[idim]
                if PropAtts[igtypdim]!={}:
                    #
                    for i in range(kelems):
                        if(ElemVals[igtypdim][i]!="-1"):
                            #
                            ielem=allElemTags[kdims][i]
                            idx=idxbeams.index(ielem)+1
                            ivaltab=ElemVals[igtypdim][i].split(' - ')
                            ifunc=ivaltab[0]+","+ivaltab[1]
                            if(not ifuncwght in INelemHydrost):
                                INelemHydrost[ifuncwght]=[]
                            #
                            tmpelem={}
                            tmpelem['val']=['HYDROBM',idx]
                            tmpelem['fmt']='(A10,I6)'

                            INelemHydrost[ifuncwght].append(tmpelem)

            except Exception as emsg:
                gmsh.logger.write("Pb in preparing Beam Hydrostatic Loads for writing:"+str(emsg), level="error")
                return -1
            NHYDROST=len(INelemHydrost)

        # Prepare Oblique Support (Structural)
        if(not self.isThermal):
            INOblique=[]
            NOBLIQUE=0
            #
            try:
                #
                idx=len(INnodes)-1 # last node index, will be used to add new nodes

                signObliq=[+1,-1]
                fieldObliq=['obliqdispl;0','obliqrot;0']

                for i0 in range(len(fieldObliq)):
                    igtypdim=fieldObliq[i0]
                    igtyp,idim=igtypdim.split(';')
                    idim=int(idim)
                    kelems=nallelems[idim]
                    kdims=nalldims[idim]
                    #
                    if PropAtts[igtypdim]!={}:
                        #
                        for i in range(kelems):
                            if(ElemVals[igtypdim][i]!="-1"):
                                ielem=allElemTags[kdims][i]
                                ientity=allElemEntityTags[kdims][i]
                                inodetag=allElemNodeTags[kdims][i][0]
                                ivaltab=ElemVals[igtypdim][i].split(' - ')
                                idx1=allNodeTags.index(inodetag) #first node of oblique
                                node1=idx1+1
                                #
                                if(ndims==2):
                                    x1=allNodeCoords[3*idx1];y1=allNodeCoords[3*idx1+1]
                                    pt2coords=ivaltab[0].split(',')
                                    dx2=float(pt2coords[0]);dy2=float(pt2coords[1])
                                else:
                                    x1=allNodeCoords[3*idx1];y1=allNodeCoords[3*idx1+1];z1=allNodeCoords[3*idx1+2]
                                    pt2coords=ivaltab[0].split(',')
                                    pt3coords=ivaltab[1].split(',')
                                    dx2=float(pt2coords[0]);dy2=float(pt2coords[1]);dz2=float(pt2coords[2])
                                    dx3=float(pt3coords[0]);dy3=float(pt3coords[1]);dz3=float(pt3coords[2])

                                # second node of oblique:
                                tmp={}
                                idx+=1
                                node2=idx+1
                                if(ndims==2):
                                    x2=x1+dx2;y2=y1+dy2
                                    tmp['val']=['NODE',node2,x2,y2]
                                    tmp['fmt']='(A10,I6,F11.4,F11.4)'
                                else:
                                    x2=x1+dx2;y2=y1+dy2;z2=z1+dz2
                                    tmp['val']=['NODE',node2,x2,y2,z2]
                                    tmp['fmt']='(A10,I6,F11.4,F11.4,F11.4)'
                                INnodes.append(tmp)
                                #
                                # third node of oblique:
                                if(ndims==3):
                                    tmp={}
                                    idx+=1
                                    node3=idx+1
                                    x3=x1+dx3;y3=y1+dy3;z3=z1+dz3
                                    tmp['val']=['NODE',node3,x3,y3,z3]
                                    tmp['fmt']='(A10,I6,F11.4,F11.4,F11.4)'
                                    INnodes.append(tmp)
#                                 idx=idxbeams.index(ielem)+1
#                                 ivaltab=ElemVals[igtypdim][i].split(' - ')
                                tmpelem={}
                                if(ndims==2):
                                    tmpelem['val']=['INCLIN',signObliq[i0]*node1,node2]
                                    tmpelem['fmt']='(A10,I6,I6)'
                                else:
                                    tmpelem['val']=['INCLIN',signObliq[i0]*node1,node2,node3]
                                    tmpelem['fmt']='(A10,I6,I6,I6)'
                                #
                                INOblique.append(tmpelem)
            except Exception as emsg:
                gmsh.logger.write("Pb in preparing Oblique for writing:"+str(emsg), level="error")
                return -1
            NOBLIQUE=len(INOblique)
        #
        #
        # FINAL WRITING OF .IN FILE (F.E., materials and constraints)
        #
        # 1/ Write header
        f=open(os.path.join(self.dir,self.INfile),'w')
        #
        f.write("InputFile created with GMSH-SAFIR Interface\n")
        #
        tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","Title1")],False)
        f.write(tmp0['values'][0]+"\n")

        tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","Title2")],False)
        f.write(tmp0['values'][0]+"\n")
        f.write("\n")
        f.write(self.writeLineFortran('(A10,I6)',['NNODE',len(INnodes)])+"\n")
        f.write(self.writeLineFortran('(A10,I6)',['NDIM',ndims])+"\n")
        #
        if(self.isThermal):
            f.write(self.writeLineFortran('(A10,I6)',['NDOFMAX',1])+"\n")
        else:
            f.write(self.writeLineFortran('(A10,I6)',['NDOFMAX',ndofmax])+"\n")
        #
        # OBSOLETE
#         f.write(self.writeLineFortran('(A10,I6,A5,I6,A5,I6,A5,I6)',['FROM',1,'TO',nnodes,'STEP',1,'NDDL',1])+"\n")
#         f.write(self.writeLineFortran('(A11)',['END_NDDL'])+"\n")
        #

#         # OBSOLETE - Only 1 SOLVER left = PARDISO
#         tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","name","PARDISO"),("props","name","NCORES")],False)
#         val=tmp0['values'][0]
#         f.write(self.writeLineFortran('(A10,I11)',['NCORES',val])+"\n")

        if self.isThermal and not istorsrun:
            f.write(self.writeLineFortran('(A10)',['TEMPERAT'])+"\n")
            #
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","TETA")],False)
            val=tmp0['values'][0]
            f.write(self.writeLineFortran('(A11,F11.4)',['TETA',val])+"\n")
            #
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","TINITIAL")],False)
            val=tmp0['values'][0]
            f.write(self.writeLineFortran('(A11,F11.4)',['TINITIAL',val])+"\n")
            #

        #
        # COMEBACK
        if not istorsrun:
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","key","Convergence")],False)
            convname=tmp0['name']
            iscomeback=convname=="COMEBACK"
            if convname=="COMEBACK":
                tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","key","Convergence"),("props","name","TIMESTEPMIN")],False)
                val=float(tmp0['values'][0])
                f.write(self.writeLineFortran('(A15,F15.1)',[convname,val])+"\n")
        # Next lines commented (2021-09-06) for sake of compatibility with SAFIR2019
#             else:
#                 f.write(self.writeLineFortran('(A15)',[convname])+"\n")

        #
        #DIAG CAPA: Use matrix diag (DIAG CAPA)
        if self.isThermal and not istorsrun:
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","DIAG CAPA")],False)
            hasdcapa=tmp0["values"]==[1]
            if hasdcapa:
                f.write(self.writeLineFortran('(A10)',['DIAG_CAPA'])+"\n")
        #
        if(ndims==2 and self.isThermal):
            if(temtyp!="NOMAKE"):
                tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","key","Type of calculation")],False)
                typcal=tmp0['name']
                typcalcode=tmp0['codename']
                _,sufftem=temtyp.split('.')
                typcalcode=typcalcode.replace('TEM',sufftem)
            else:
               typcal="USE_CURVES"

            if istorsrun:
                typcalcode="TORSION"

            #
            f.write(self.writeLineFortran('(A15)',[typcalcode])+"\n")
            if(typcal=="USE_LOCAFI" or typcal=="USE_HASEMI" or typcal=="USE_CFD") and not istorsrun:
                tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","name",typcal),("props","name","Expected name of the structural .IN File")],False)
                structfile=tmp0['values'][0]
                tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","name",typcal),("props","name","IELEMTYPE")],False)
                ielem=int(tmp0['values'][0])
                f.write(self.writeLineFortran('(A15)',[structfile])+"\n")
                if(sufftem=="TSH"):
                    preftype="SHELL_TYPE"
                elif(sufftem=="TEM"):
                    preftype="BEAM_TYPE"
                f.write(self.writeLineFortran('(A10,I6)',[preftype,ielem])+"\n")

        #
        else:
            typcal="USE_CURVES"


        if(not self.isThermal):
            # Loads
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","key","Mode")],False)
            modename=tmp0['name']
            modecode=tmp0['codename']
            f.write(self.writeLineFortran('(A15)',[modecode])+"\n")
            #
            # NLOAD
            f.write(self.writeLineFortran('(A5,I6)',['NLOAD',NLOAD])+"\n")
            #
            # HYDROST
            f.write(self.writeLineFortran('(A7,I6)',['HYDROST',NHYDROST])+"\n")
            #
            # OBLIQUE
            f.write(self.writeLineFortran('(A7,I6)',['OBLIQUE',NOBLIQUE])+"\n")


        #
        #MATS
        f.write(self.writeLineFortran('(A4,I3)',['NMAT',len(self.listMats)])+"\n")
        #
        f.write(self.writeLineFortran('(A11)',['ELEMENTS'])+"\n")
        #
        if(self.isThermal): # Header (Thermal)
            f.write(self.writeLineFortran('(A5,I6)',['SOLID',nelems])+"\n")
            #
            f.write(self.writeLineFortran('(A2,I6)',['NG',2])+"\n")
            #
            if(self.isThermal and ndims==2):
                self.nvoids=len(PropAtts['void;1'])
                f.write(self.writeLineFortran('(A5,I6)',['NVOID',self.nvoids])+"\n")
                if(self.nvoids>0):
                    f.write(self.writeLineFortran('(A11,I6)',['FRTIERVOID',nfrontiervoids])+"\n")
        #
        else: # Header (Structural)
            #
            # Beams
            if(len(INelemBeams)>0):
                f.write(self.writeLineFortran('(A4,I6,I6)',['BEAM',NBEAM,NGEOBEAM])+"\n")
                #
                # NG Beam
                tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","NG BEAM")],False)
                val=int(tmp0['values'][0])
                f.write(self.writeLineFortran('(A2,I6)',['NG',val])+"\n")
                #
                # NFIBER
                f.write(self.writeLineFortran('(A6,I6)',['NFIBER',NFIBER])+"\n")
            #
            # Shells
            if(len(INelemShells)>0):
                f.write(self.writeLineFortran('(A5,I6,I6)',['SHELL',NSHELL,NGEOSHELL])+"\n")
                #
                # NG Shells
                if(ndims==3):
                    tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","NG SHELLTHICK")],False)
                    val=int(tmp0['values'][0])
                else:
                    val=0
                f.write(self.writeLineFortran('(A7,I6)',['NGTHICK',val])+"\n")
                #
                # Shell rebars
                f.write(self.writeLineFortran('(A7,I6)',['NREBARS',NREBARS])+"\n")
            #
            # Solids
            if(len(INelemSolid)>0 or self.isThermal):
                f.write(self.writeLineFortran('(A6,I6)',['SOLID',NSOLID])+"\n")
                #
                # NG Solids
                if(ndims==3):
                    tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","NG SOLID")],False)
                    val=int(tmp0['values'][0])
                else:
                    val=0
                f.write(self.writeLineFortran('(A2,I6)',['NG',val])+"\n")
            #
            # Truss
            if(len(INelemTruss)>0):
                f.write(self.writeLineFortran('(A5,I6,I6)',['TRUSS',NTRUSS,NGEOTRUSS])+"\n")
            #
            # Springs (TBD)
            #

        #
        f.write(self.writeLineFortran('(A11)',['END_ELEM'])+"\n")
        #
        # 2/ Write down all nodes (Thermal and Structural)
        f.write(self.writeLineFortran('(A10)',['NODES'])+"\n")
        for i in range(len(INnodes)):
            ivals=[]
            for ival in range(len(INnodes[i]['val'])):
                if(ival>1):
                    ivals.append("%.6f" % float(INnodes[i]['val'][ival]))
                else:
                    ivals.append(INnodes[i]['val'][ival])
            f.write(self.writeLineFortran(INnodes[i]['fmt'],ivals)+"\n")

        #
        # 3/ Write nodelines (Thermal 2D only)
        if(ndims==2 and self.isThermal and not istsh):
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","Global center (Yo)")],False)
            y0=tmp0['values'][0]
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","Global center (Xo)")],False)
            z0=tmp0['values'][0]
            #
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","Center of torsion (Yc)")],False)
            yc=tmp0['values'][0]
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","Center of torsion (Xc)")],False)
            zc=tmp0['values'][0]
            #
            if(typcal=="USE_CURVES" or typcal=="USE_HASEMI"  or typcal=="USE_LOCAFI" and not istorsrun) or istorsrun:
                f.write(self.writeLineFortran('(A10,F5.1,F5.1)',['NODELINE',float(y0),float(z0)])+"\n")
                f.write(self.writeLineFortran('(A10,F5.1,F5.1)',['YC_ZC',float(yc),float(zc)])+"\n")
            #
            #
        # 4/ Write fixations (Thermal and Structural)
        f.write(self.writeLineFortran('(A10)',['FIXATIONS'])+"\n")
        #
        for i in range(len(INfixnodes)):
            f.write(self.writeLineFortran(INfixnodes[i]['fmt'],INfixnodes[i]['val'])+"\n")
        #
        for i in range(len(SAMEnodes)):
            f.write(self.writeLineFortran(SAMEnodes[i]['fmt'],SAMEnodes[i]['val'])+"\n")
        f.write(self.writeLineFortran('(A10)',['END_FIX'])+"\n")

        # Write F.E. and constraints, separately for Thermal and Structural
        if(self.isThermal): # Write F.E. and constraints (Thermal)
            # 5/ Write elems (Thermal)
            f.write(self.writeLineFortran('(A10)',['NODOFSOLID'])+"\n")
            for i in range(len(INelems)):
                f.write(self.writeLineFortran(INelems[i]['fmt'],INelems[i]['val'])+"\n")

            #6 /Write Frontiers (Thermal)
            if not istorsrun:
                f.write(self.writeLineFortran('(A10)',['FRONTIER'])+"\n")
                for i in range(len(INfrontiers)):
                    f.write(self.writeLineFortran(INfrontiers[i]['fmt'],INfrontiers[i]['val'])+"\n")
                    #
                f.write(self.writeLineFortran('(A10)',['END_FRONT'])+"\n")

            # 7/ Write Voids (Thermal 2D)
            if(ndims==2 and self.nvoids>0):
                for ivoid,tmpvoid in INvoids.items():
                    f.write(self.writeLineFortran('(A10)',['VOID'])+"\n")
                    for i in range(len(tmpvoid)):
                        f.write(self.writeLineFortran(tmpvoid[i]['fmt'],tmpvoid[i]['val'])+"\n")
                    f.write(self.writeLineFortran('(A10)',['END_VOID'])+"\n")

            #8/ Write Symmetries (Thermal)
            f.write(self.writeLineFortran('(A10)',['SYMMETRY'])+"\n")

            # Write Realsym (Thermal 2D)
            if(ndims==2):
                try:
                    for k,v in syms['real_sym;1'].items():
                        f.write(self.writeLineFortran('(A10,I6,I6)',['REALSYM',v[0],v[1]])+"\n")
                except Exception as emsg:
                    gmsh.logger.write("Pb in writing real symmetry axis:"+str(emsg), level="error")
                    return -1

            #Write VoidSym (Thermal 2D)
            if(ndims==2 and self.nvoids>0):
                try:
                    for k,v in syms['void_sym;1'].items():
                        val=symvals['void_sym;1'][k]
                        f.write(self.writeLineFortran('(A10,I6,I6,I6)',['SYMVOID',v[0],v[1],val])+"\n")
                except Exception as emsg:
                    gmsh.logger.write("Pb in writing void symmetry axis:"+str(emsg), level="error")
                    return -1

            f.write(self.writeLineFortran('(A10)',['END_SYM'])+"\n")
        #
        else:  # Write F.E. and constraints (Structural)
            #
            # Write Beams (Structural)
            if(len(INelemBeams)>0):
                f.write(self.writeLineFortran('(A10)',['NODOFBEAM'])+"\n")
                #
                for i in range(len(INsectionBeams)):
                    imat=INsectionBeams[i]
                    ifile=imat.split(' - ')[0].strip()
                    imatstr=imat.split(' - ')[1].strip()
                    f.write(self.writeLineFortran('(A20)',[ifile])+"\n")
                    imattab=imatstr.strip().split() #Split on spaces
                    for k in range(len(imattab)):
                        iglomat=[i0 for i0 in range(len(self.listMats)) if list(self.listMats[i0].keys())[0].split('/')[0]==imattab[k]+";1"][0]
                        f.write(self.writeLineFortran('(A9,I11,I11)',['TRANSLATE',k+1,iglomat+1])+"\n")
                    f.write(self.writeLineFortran('(A9)',['END_TRANS'])+"\n")
                #
                for i in range(len(INelemBeams)):
                    f.write(self.writeLineFortran(INelemBeams[i]['fmt'],INelemBeams[i]['val'])+"\n")

            # Write Solid (Structural)
            if(len(INelemSolid)>0):
                f.write(self.writeLineFortran('(A10)',['NODOFSOLID'])+"\n")
                f.write(self.writeLineFortran('(A10)',[self.SolidFilename])+"\n")
                for i in range(len(INelemSolid)):
                    f.write(self.writeLineFortran(INelemSolid[i]['fmt'],INelemSolid[i]['val'])+"\n")

            #
            # Write Shells (Structural)
            if(len(INelemShells)>0):
                f.write(self.writeLineFortran('(A10)',['NODOFSHELL'])+"\n")
                #
                for i in range(len(INsectionShells)):
                     ikey=INsectionShells[i]
                     imat,irebar=ikey.split("//")
                     ifile,thick,zzero,imatstr=imat.split(' - ')
                     nbar,matrebar,sectrebar,levrebar,strangles=irebar.split('/')

                     f.write(self.writeLineFortran('(A10)',[ifile])+"\n")
                     f.write(self.writeLineFortran('(A10,F10.3)',["THICKNESS",float(thick)])+"\n")
                     f.write(self.writeLineFortran('(A10,F10.3)',["ZZERO",float(zzero)])+"\n")
                     iglomat=[i0 for i0 in range(len(self.listMats)) if list(self.listMats[i0].keys())[0].split('/')[0]==imatstr+";2"][0]
                     f.write(self.writeLineFortran('(A10,I3)',["MATERIAL",iglomat+1])+"\n")
                     f.write(self.writeLineFortran('(A10,I3)',["REBARS",nbar])+"\n")
                     imattab=matrebar.strip().split() #Split on spaces
                     isecttab=sectrebar.strip().split() #Split on spaces
                     ilevtab=levrebar.strip().split() #Split on spaces
                     angles=ast.literal_eval(strangles)
                     #
                     for k in range(len(imattab)):
                         iglomat=[i0 for i0 in range(len(self.listMats)) if list(self.listMats[i0].keys())[0].split('/')[0]==imattab[k]+";1"][0]
                         f.write(self.writeLineFortran('(A20,I3)',["REBARMAT",iglomat+1])+"\n")
                         f.write(self.writeLineFortran('(A20,F10.3)',["SECTION",float(isecttab[k])])+"\n")
                         f.write(self.writeLineFortran('(A20,F10.3)',["LEVEL",float(ilevtab[k])])+"\n")
                         iangle=[val for i,val in angles.items() if i==k][0]
                         if(type(iangle)==list):
                            f.write(self.writeLineFortran('(A20,F10.3,F10.3,F10.3)',["NORMAL",iangle[0],iangle[1],iangle[2]])+"\n")
                         else:
                            f.write(self.writeLineFortran('(A20,F10.3)',["ANGLE",iangle])+"\n")
                     #
                for i in range(len(INelemShells)):
                    f.write(self.writeLineFortran(INelemShells[i]['fmt'],INelemShells[i]['val'])+"\n")
            #

            # Write Truss (Structural)
            if(len(INelemTruss)>0):
                f.write(self.writeLineFortran('(A10)',['NODOFTRUSS'])+"\n")
                #
                for i in range(len(INgroupTruss)):
                    iparam=INgroupTruss[i]
                    ifile=iparam.split(' - ')[0].strip()
                    isect=iparam.split(' - ')[1].strip()
                    ires=iparam.split(' - ')[2].strip()
                    imat=iparam.split(' - ')[3].strip()
                    iglomat=[i0 for i0 in range(len(self.listMats)) if list(self.listMats[i0].keys())[0].split('/')[0]==imat+";1"][0]
                    f.write(self.writeLineFortran('(A10,F10.3,F10.3,I3)',[ifile,float(isect),float(ires),iglomat+1])+"\n")
                #
                for i in range(len(INelemTruss)):
                    f.write(self.writeLineFortran(INelemTruss[i]['fmt'],INelemTruss[i]['val'])+"\n")

            #
            # Write Oblique Supports (Structural) (also ok with Pardiso solver, though documentation says only possible with Cholesky solver)
            if(len(INOblique)>0):
                for i in range(len(INOblique)):
                    f.write(self.writeLineFortran(INOblique[i]['fmt'],INOblique[i]['val'])+"\n")
                f.write(self.writeLineFortran('(A10)',['END_INCLIN'])+"\n")


            # Write Beam Relaxations (Structural)
            if(len(INelemRelax)>0):
                f.write(self.writeLineFortran('(A10)',['RELAX_ELEM'])+"\n")
                f.write(self.writeLineFortran('(A15)',['BEAMS'])+"\n")
                for i in range(len(INelemRelax)):
                    f.write(self.writeLineFortran(INelemRelax[i]['fmt'],INelemRelax[i]['val'])+"\n")
                f.write(self.writeLineFortran('(A9)',['END_BEAMS'])+"\n")
                f.write(self.writeLineFortran('(A9)',['END_RELAX'])+"\n")

        #
        #
        tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","PRECISION")],False)
        prec=float(tmp0['values'][0])
        f.write(self.writeLineFortran('(A9,E10.1)',['PRECISION',prec])+"\n")

        if(not self.isThermal):
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","Consider max displacement")],False)
            if tmp0['values'][0]==1 :
                tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","MAX DISPL")],False)
                maxdispl=float(tmp0['values'][0])
                f.write(self.writeLineFortran('(A9,E10.1)',['MAX_DISPL',maxdispl])+"\n")
        #

        if(not self.isThermal):
            #
            # Write Loads (Structural)
            if(len(INelemLoads)>0):
                f.write(self.writeLineFortran('(A5)',['LOADS'])+"\n")
                for ifunc in INelemLoads:
                    f.write(self.writeLineFortran('(A10,A10)',['FUNCTION',ifunc])+"\n")
                    for i in range(len(INelemLoads[ifunc])):
                        f.write(self.writeLineFortran(INelemLoads[ifunc][i]['fmt'],INelemLoads[ifunc][i]['val'])+"\n")
                    f.write(self.writeLineFortran('(A10)',['END_LOAD'])+"\n")

            # Write Beam Hydrostatic Loads (Structural)
            if(len(INelemHydrost)>0):
                for ifuncwght in INelemHydrost:
                    ifunc,iweight=ifuncwght.split(',')
                    f.write(self.writeLineFortran('(A10,A10)',['WATERTABLE',ifunc])+"\n")
                    f.write(self.writeLineFortran('(A10,A10)',['SPECWEIGHT',iweight])+"\n")
                    for i in range(len(INelemHydrost[ifuncwght])):
                        f.write(self.writeLineFortran(INelemHydrost[ifuncwght][i]['fmt'],INelemHydrost[ifuncwght][i]['val'])+"\n")
                f.write(self.writeLineFortran('(A10)',['END_HYDRO'])+"\n")

            # Write Mass (Structural)
            if(len(INelemMass)>0):
                f.write(self.writeLineFortran('(A10)',['MASS'])+"\n")
                for i in range(len(INelemMass)):
                    f.write(self.writeLineFortran(INelemMass[i]['fmt'],INelemMass[i]['val'])+"\n")
                f.write(self.writeLineFortran('(A10)',['END_MASS'])+"\n")

        #
        # Write materials (Thermal and Structural)
        #
        f.write(self.writeLineFortran('(A10)',['MATERIALS'])+"\n")
        try:
            #
            for i in range(len(self.listMats)):
                iprop=self.listMats[i]
                imatstr=list(iprop.keys())[0]
                imat=imatstr.split('/')[1].split("-")[-1].upper()
                tmpvals=list(iprop.values())[0]
                #
                if not istorsrun:
                    #
                    if not 'User-defined' in imatstr:
                        f.write(self.writeLineFortran('(A10)',[imat])+"\n")
                        #
                        vallst=[];fmtstr="("
                        #
                        print("ndim=",ndims,", isTherm=",self.isThermal,", len(tmpvals)=",len(tmpvals),": ",tmpvals)
                        if ndims==2 and self.isThermal:
                            leng1=len(tmpvals)-5 #Remove from the list the material name, the torsname, the Young module and Poisson coeff (and also the material name and torsname)
                        #
                        elif(self.isThermal):
                            leng1=len(tmpvals)-2 #Remove from the list the material name and torsname
                        else:
                            leng1=len(tmpvals)-1 # Remove from the list the material name (no torsname)
                        #
                        begin=True
                        if(leng1>0):
                            for i0 in range(leng1):
                                key=list(tmpvals[i0].keys())[0]
                                if(re.search("^0",key)==None): #Reserved to menus, not to params].keys())[0]
                                    val0=list(tmpvals[i0].values())[0][0]
                                    vallst.append(val0)
                                    if str(val0).replace('.','',1).isdigit():
                                        format1="F15.2"
                                    else:
                                        format1="A15"
                                    if(begin):
                                        fmtstr+=format1
                                        begin=False
                                    else:
                                        fmtstr+=","+format1
                            fmtstr+=")"
                            f.write(self.writeLineFortran(fmtstr,vallst)+"\n")
                        #
                        if 'STAINLESS STEELS' in imat:
                            f.write(self.writeLineFortran('(A9)',["SLS1.4301"])+"\n")
                            f.write(self.writeLineFortran('(F15.2,F15.2,F15.2)',[25.,4.,0.4])+"\n")
                        #
                        if 'ALUMINUM' in imat:
                            f.write(self.writeLineFortran('(A9)',["AL6061_T6"])+"\n")
                            f.write(self.writeLineFortran('(F15.2,F15.2,F15.2)',[25.,4.,0.7])+"\n")
                    #
                    else:# User-defined material
                        ikey=[i for i in range(len(tmpvals)) if "Filename" in list(tmpvals[i].keys())[0]][0]
                        fname=list(tmpvals[ikey].values())[0][0]
                        #
                        if os.path.exists(os.path.join(self.dir,fname)):
                            fn=os.path.join(self.dir,fname)
                        elif os.path.exists(fname):
                            fn=fname
                        else:
                            gmsh.logger.write("User-defined material: Pb with inexistant file:"+fname, level="error")
                            return -1
                        f0=open(fn,'r')
                        #
                        try:
                            lines=f0.readlines()
                            if(lines==[]):
                                raise ValueError("Empty file")
                            tmpl=re.split('\s+',lines[0].replace('\n',''))
                            pattern=re.compile("USER.*[0-9]+$")
                            if((not len(tmpl)==2) or re.search(pattern,lines[0])==None):
                                raise ValueError("First line shall be in the form: USER[X] [nb]")
                            inam=tmpl[0]
                            inb=int(tmpl[1])
                            if(inb+1!=len(lines) or inb<2):
                                raise ValueError("Incorrect number of lines")
                            tmpl=re.split('\s+',lines[1].replace('\n',''))
                            if(len(tmpl)!=11):
                                raise ValueError("Second line shall contain 9 parameters: T,lambda,c,rho,q,Tstart,Tend,hc,hf,emissiv,r")
                            for iline in lines[2:]:
                                tmpl=re.split('\s+',iline.replace('\n',''))
                                if(len(tmpl)!=4):
                                    raise ValueError("From third line on, it shall contain 4 parameters: T,lambda,c,rho")
                            # Success in reading
                            for iline in lines:
                                f.write(iline)
                        except Exception as emsg:
                            raise ValueError("User-defined material: Pb in file "+fname+": "+str(emsg))
                        f0.close()

                #
                else:
                    torsname=[list(k.values())[0] for k in tmpvals if "torsname" in list(k.keys())[0]][0][0]
                    #
                    # Write imat and not torsname, because SAFIR knows that, and this name is just for better viewing materials in the .IN file
                    if("DEFINED" in imat):
                        imat="USER-DEFINED"
                    f.write(self.writeLineFortran('(A12)',[imat])+"\n")
                    #
                    if(not "INSULATION" in torsname):
                        #
                        torsparams=['Young module','Poisson coefficient']
                        vallst=[];fmtstr="("
                        for i in range(len(torsparams)):
                            iparam=torsparams[i]

                            if(i==0):
                                fmtstr+="F15.2"
                            else:
                                fmtstr+=",F15.2"
                            ikey=[i0 for i0 in range(len(tmpvals)) if iparam in list(tmpvals[i0].keys())[0]][0]
                            vallst.append(list(tmpvals[ikey].values())[0][0])
                        fmtstr+=")"
                        f.write(self.writeLineFortran(fmtstr,vallst)+"\n")
                #
        except Exception as emsg:
            gmsh.logger.write("Pb in writing materials:"+str(emsg), level="error")
            return -1

        # Write final elements in .IN file (run duration...)

        if not (self.isThermal and istorsrun):
            f.write(self.writeLineFortran('(A10)',['TIME'])+"\n")
            #
            if iscomeback:
                tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","key","Convergence"),("props","name","TIMESTEP,UPTIME,TIMESTEPMAX")],False)
                tstep,uptime,tstepmax=tmp0['values'][0].split(",")
                tstep=float(tstep);uptime=float(uptime);tstepmax=float(tstepmax)
                f.write(self.writeLineFortran('(I6,I6,I6)',[tstep,uptime,tstepmax])+"\n")
            else:
                tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","key","Convergence"),("props","name","TIMESTEP,UPTIME(1)")],False)
                tstep,uptime=tmp0['values'][0].split(",")
                tstep=float(tstep);uptime=float(uptime)
                f.write(self.writeLineFortran('(I6,I6)',[tstep,uptime])+"\n")
                tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","key","Convergence"),("props","name","TIMESTEP,UPTIME(2)")],False)
                tstep,uptime=tmp0['values'][0].split(",")
                tstep=float(tstep);uptime=float(uptime)
                f.write(self.writeLineFortran('(I6,I6)',[tstep,uptime])+"\n")
            #
            f.write(self.writeLineFortran('(A10)',['END_TIME'])+"\n")
            #
            if not self.isThermal:
                tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","Thermal elongation")],False)
                valnum=tmp0['values'][0]
                lbls=tmp0['valueLabels']
                val0=[k for k,v in lbls.items() if v==valnum][0]
                f.write(self.writeLineFortran('(A7)',[val0])+"\n")
            #
            f.write(self.writeLineFortran('(A10)',['IMPRESSION'])+"\n")
            f.write(self.writeLineFortran('(A10)',['TIMEPRINT'])+"\n")
            #
            tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("props","name","TIMEPRINT,UPTIMEPRINT")],False)
            tstep,uptime=tmp0['values'][0].split(",")
            tstep=float(tstep);uptime=float(uptime)
            f.write(self.writeLineFortran('(I6,I6)',[tstep,uptime])+"\n")
            f.write(self.writeLineFortran('(A10)',['END_TIMEPR'])+"\n")

        # Write the different prints
        if not self.isThermal:
            oprints=["PRINTDEPL","PRINTTMPRT","PRINTVELAC","PRINTFHE","PRINTREACT","PRINTMN","PRNEIBEAM","PRINTSHELL","PRNNXSHELL","PRNMXSHELL","PRNEASHELL","PRNEISHELL"]
            #
            for ipo in oprints:
                print('ipo=',ipo)
                tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","key","outputs"),("props","name",ipo+ ' Print')],False)
                hasprint=tmp0["values"]==[1]
                if hasprint:
                    f.write(self.writeLineFortran('(A10)',[ipo])+"\n")
                    #
                    if(ipo=="PRINTDEPL" or ipo=="PRINTFHE"):
                        tmp0=self.getDBValue(self.safirDB,[("children","name",self.pbType),("children","key","outputs"),("props","name",ipo+ ' Tstart')],False)
                        val=int(tmp0["values"][0])
                        f.write(self.writeLineFortran('(I6)',[val])+"\n")
        #
        f.close()

        gmsh.logger.write("Create SAFIR .IN file with the given parameters... DONE", level="info")
        #
        if self.launchSAFIR:
            gmsh.logger.write("Launch SAFIR exe... ", level="info")
            #
            INfile_noext=os.path.splitext(self.INfile)[0]
            cmd="cd "+self.dir+";"+os.environ['SAFIREXE']+" "+INfile_noext
            p = subprocess.Popen(cmd, stdout = subprocess.PIPE, stderr = subprocess.STDOUT, shell=True)
            while p.poll() is None:
                iline = p.stdout.readline()
                gmsh.logger.write(iline, level="info")
            #
        return 0


    def eventLoop(self):
        # terminate the event loop if the GUI was closed
        if gmsh.fltk.isAvailable() == 0: return 0
        # wait for an event
        gmsh.fltk.wait()
        #
        # Revise input files (to monitore changes occured after the user has made changes using menus 'Open...', 'New' or 'Open Recent')
        tmp=gmsh.model.getFileName()
        if(tmp!=self.geofile):
            self.geofile=tmp
            gmsh.open(self.geofile)
            self.dir=os.path.dirname(self.geofile)
            #if(TOTO):
            filetmp=os.path.basename(self.geofile)
            isGeo=os.path.splitext(self.geofile)[1]=='.igeo'
            if(isGeo):
                self.g4sfile=self.geofile.replace(".geo",".g4s")
                self.INfile=self.geofile.replace(".geo",".IN")
            else:
                self.g4sfile=os.path.splitext(self.geofile)[0]+'.g4s'
                self.INfile=os.path.splitext(self.geofile)[0]+'.IN'
            #
            #
            if(os.path.exists(self.g4sfile)):
                self.getG4sJson(self.g4sfile) # if existing DB in input directory
                self.recreateContextMenusFromDB(self.pbType,True)
                #
                self.isThermal="Thermal" in self.pbType
                print("self.isThermal=",self.isThermal)
                #
            else:
                self.contextDB=json.loads(contextDBstring) # load ContextDB from this script
                self.initCompleteContextDB(self.contextDB) # Copy Materials: same for Volume/th3D than Surface/th2D
                self.safirDB=json.loads(safirDBstring)
                self.initCompleteSafirDB(self.safirDB)
                self.pbType="Thermal 2D" #Initialization of problem type

                gmsh.onelab.clear()
                #
                self.updateGeneralLists()
                self.loadContextDB(self.contextDB,self.pbType,True)
                self.loadSafirDB()
                self.loadInspectDB(self.pbType)
                s=deepcopy(json.loads(gmsh.onelab.get().replace("\\","/"))["onelab"]["parameters"])
                self.params= [k for k in s if 'SAFIR' in k['name'] or self.pbType in k['name']]


            gmsh.fltk.update()

        # Action requested: three types of actions are managed:
        # 1/ Check: store in memory the changes of ContextDB which are not yet confirmed to be stored on the disk (except for SafirDB stored at every step)
        # 2/ Add(update)/Remove: confirm actions in the disk storage of ContextDB
        # 3/ Inspect: generate views of objects that have been designed in the Drawing Window
        #
        # Add/Remove is always with Template, so that it is everytime instanciated to the pg/ent number by the GMSH-core code.
        # This has for advantage to always directly know which pg/ent is concerned.
        # The inconvenient is that, due to its "always template" aspect, the individual infos cannot be stored (it would have needed an additional object of ContextDB in memory)
        # Check, on the opposite, cannot deliver directly the pg/ent identification, it requires to be detetrmined as a difference with the previous Chek menus.
        # But the individual infos can be kept in these menus.

        action = gmsh.onelab.getString("ONELAB/Action")

        if len(action) < 1:
            # no action requested
            pass
        elif action[0] == "check":
             gmsh.onelab.setString("ONELAB/Action", [""])
             rc=self.manageContextMenus()
             gmsh.fltk.update()

        elif "inspect" in action[0]:
             _,ctyp=action[0].split(" ")
             gmsh.onelab.setString("ONELAB/Action", [""])
             if(ctyp!="clean"):
                 rc=self.manageInspect(ctyp)
             else:
                 self.cleaningToClean()
             gmsh.graphics.draw()

        elif "add" in action[0]:
            self.add_or_remove=1 # Add
            #
#             oldps=[]
#             for k in self.params:
#                 if('attributes' in k):
#                     if 'ONELAB Context' in k['name'] and [i for i,(k0,v0) in enumerate(k['attributes'].items()) if k0=="Aspect" and v0=="Button"]!=[]:
#                         oldps.append(k)
#             print('oldps=',oldps)
            #
            rc=self.manageStoreDB(action[0])
            gmsh.onelab.setString("ONELAB/Action", [""])

        elif "remove" in action[0]:
            self.add_or_remove=0 # Remove
            #
#             oldps=[]
#             for k in self.params:
#                 if('attributes' in k):
#                     if 'ONELAB Context' in k['name'] and [i for i,(k0,v0) in enumerate(k['attributes'].items()) if k0=="Aspect" and v0=="Button"]!=[]:
#                         oldps.append(k)
#             print('oldps=',oldps)
            #
            rc=self.manageStoreDB(action[0])
            gmsh.onelab.setString("ONELAB/Action", [""])

        elif "draw" in action[0]:
            rc=self.drawLAX(action[0])
            gmsh.onelab.setString("ONELAB/Action", [""])

        elif action[0] == "run":
            # user clicked on "Run"
            gmsh.onelab.setString("ONELAB/Action", [""])
            rc=self.createIN()


        elif action[0] == "viewg4s":
            # user clicked on "Run"
            gmsh.onelab.setString("ONELAB/Action", [""])
            rc=self.viewAndWriteInfog4s(1)


        elif action[0] == "reloadprops":
            # user clicked on "Run"
            gmsh.onelab.setString("ONELAB/Action", [""])
            if(self.g4sfile!="" and os.path.exists(self.g4sfile)):
            #if(1>0):
                self.getG4sJson(self.g4sfile)
                self.recreateContextMenusFromDB(self.pbType,True)
            else:
                gmsh.logger.write("No existing G4S file to load", level="error")
        return 1



baseparameters="""
  [
  {
    "type":"string",
    "name":"ONELAB/Button",
    "values":["Create SAFIR .IN file", "run"],
    "visible":false
  }
]"""

#   {
#     "type":"number",
#     "name":"0Modules/Solver/SAFIR/0Problem type",
#     "values":[0],
#     "choices":[0, 1,2,3,4],
#     "valueLabels":{"Thermal2D": 0, "Thermal3D": 1, "Structural2D": 2, "Structural3D": 3, "Tshell": 4}
#   },



safirDBstring="""
{
"name":"allProblemData",
"key":"",
"props":[
    {"name":"Also run SAFIR?","type":"number","values":[0],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1}}
    ],
"children":[
    {
    "key":"Problem Type","name":"Thermal 2D",
    "props":[
        {"name":"Title1","type":"string","values":["Safir_Thermal_Analysis"]},
        {"name":"Title2","type":"string","values":["Mesh_from_G4S-Mesher"]},
        {"name":"PRECISION","type":"number","values":[1.0e-3],"min":0,"max":1.0e-1,"step":1.0e-3},
        {"name":"TETA","type":"number","values":[0.9],"min":0,"max":1,"step":0.1,"visible":true},
        {"name":"TINITIAL","type":"number","values":[20],"min":0,"max":1,"step":0.1,"visible":true},
        {"name":"TIMEPRINT,UPTIMEPRINT","type":"string","values":["30,3600"],"visible":true},
        {"name":"Run torsion analysis","type":"number","values":[0],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1}},
        {"name":"Use matrix diag (DIAG CAPA)","type":"number","values":[1],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1},"visible":true},
        {"name":"Global center (Xo)","type":"number","values":[0],"min":0,"max":100,"step":1,"visible":true},
        {"name":"Global center (Yo)","type":"number","values":[0],"min":0,"max":100,"step":1,"visible":true},
        {"name":"Center of torsion (Xc)","type":"number","values":[0],"min":0,"max":100,"step":1,"visible":true},
        {"name":"Center of torsion (Yc)","type":"number","values":[0],"min":0,"max":100,"step":1,"visible":true},
        {"name":"Name of the .IN File","type":"string","values":["untitled.IN"]}
    ],
    "children":[
        {
        "key":"Convergence","name":"COMEBACK",
        "props":[
            {"name":"TIMESTEPMIN","type":"number","values":[1.0e-5],"min":0,"max":1.0e-3,"step":1.0e-7,"visible":true},
            {"name":"TIMESTEP,UPTIME,TIMESTEPMAX","type":"string","values":["1,3600,8"],"visible":true}
        ],
        "children":[]
        },
        {
        "key":"Convergence","name":"NOCOMEBACK",
        "props":[
            {"name":"TIMESTEP,UPTIME(1)","type":"string","values":["12,1800"],"visible":true},
            {"name":"TIMESTEP,UPTIME(2)","type":"string","values":["20,3600"],"visible":true}
        ],
        "children":[]
        },
        {
        "key":"TEM-TSH","name":"MAKE.TEM",
        "props":[],
        "children":[]
        },
        {
        "key":"TEM-TSH","name":"MAKE.TSH",
        "props":[],
        "children":[]
        },
        {
        "key":"TEM-TSH","name":"NOMAKE",
        "props":[],
        "children":[]
        },
        {
        "key":"Type of calculation","name":"USE_CURVES","codename":"MAKE.TEM",
        "props":[
            ],
        "children":[]
        },
        {
        "key":"Type of calculation","name":"USE_LOCAFI","codename":"MAKE.TEMLF",
        "props":[
            {"name":"Expected name of the structural .IN File","type":"string","values":["structural.IN"],"visible":true},
            {"name":"IELEMTYPE","type":"number","values":[1],"min":0,"max":100,"step":1,"visible":true}
        ],
        "children":[]
        },
        {
        "key":"Type of calculation","name":"USE_HASEMI","codename":"MAKE.TEMHA",
        "props":[
            {"name":"Expected name of the structural .IN File","type":"string","values":["structural.IN"],"visible":true},
            {"name":"IELEMTYPE","type":"number","values":[1],"min":0,"max":100,"step":1,"visible":true}
        ],
        "children":[]
        },
        {
        "key":"Type of calculation","name":"USE_CFD","codename":"MAKE.TEMCD",
        "props":[
            {"name":"Expected name of the structural .IN File","type":"string","values":["structural.IN"],"visible":true},
            {"name":"IELEMTYPE","type":"number","values":[1],"min":0,"max":100,"step":1,"visible":true}
        ],
        "children":[]
        }
    ]},
    {
    "key":"Problem Type","name":"Thermal 3D",
    "props":[
        {"name":"Title1","type":"string","values":["Safir_Thermal_3D_Analysis"]},
        {"name":"Title2","type":"string","values":["Mesh_from_G4S-Mesher"]},
        {"name":"PRECISION","type":"number","values":[1.0e-3],"min":0,"max":1.0e-1,"step":1.0e-3},
        {"name":"TETA","type":"number","values":[0.9],"min":0,"max":1,"step":0.1},
        {"name":"TINITIAL","type":"number","values":[20],"min":0,"max":1,"step":0.1},
        {"name":"TIMEPRINT,UPTIMEPRINT","type":"string","values":["30,3600"]},
        {"name":"Use matrix diag (DIAG CAPA)","type":"number","values":[0],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1},"visible":true},
        {"name":"Name of the .IN File","type":"string","values":["untitled.IN"]}
    ],
    "children":[
        {
        "key":"Convergence","name":"COMEBACK",
        "props":[
            {"name":"TIMESTEPMIN","type":"number","values":[1.0e-5],"min":0,"max":1.0e-3,"step":1.0e-7,"visible":true},
            {"name":"TIMESTEP,UPTIME,TIMESTEPMAX","type":"string","values":["1,3600,8"],"visible":true}
        ],
        "children":[]
        },
        {
        "key":"Convergence","name":"NOCOMEBACK",
        "props":[
            {"name":"TIMESTEP,UPTIME(1)","type":"string","values":["12,1800"],"visible":true},
            {"name":"TIMESTEP,UPTIME(2)","type":"string","values":["20,3600"],"visible":true}
        ],
        "children":[]
        }
    ]},
    {
    "key":"Problem Type","name":"Structural 2D",
    "props":[
        {"name":"Title1","type":"string","values":["Safir_Structural_Analysis"]},
        {"name":"Title2","type":"string","values":["Mesh_from_G4S-Mesher"]},
        {"name":"Name of the .IN File","type":"string","values":["untitled.IN"]},
        {"type":"number","name":"Consider max displacement","values":[0],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1}},
        {"type":"number","name":"MAX DISPL","values":[999],"min":1,"max":1000,"step":1,"visible":false},
        {"name":"PRECISION","type":"number","values":[1.0e-3],"min":0,"max":1.0e-1,"step":1.0e-3},
        {"name":"NG BEAM","type":"number","values":[2],"min":0,"max":20,"step":1},
        {"name":"Thermal elongation","valueLabels":{"NOEPSTH":0,"EPSTH":1},"choices":[0,1],"type":"number","values":[1]},
        {"name":"TIMEPRINT,UPTIMEPRINT","type":"string","values":["30,3600"]}
        ],
    "children":[
        {
        "key":"Mode","name":"DYNAMIC PURE NR","codename":"DYNAMIC PURE_NR",
        "props":[
        ],
        "children":[]
        },
        {
        "key":"Mode","name":"DYNAMIC APPR NR","codename":"DYNAMIC APPR_NR",
        "props":[
        ],
        "children":[]
        },
        {
        "key":"Mode","name":"STATIC PURE NR","codename":"STATIC PURE_NR",
        "props":[],
        "children":[]
        },
        {
        "key":"Mode","name":"STATIC APPR NR","codename":"STATIC APPR_NR",
        "props":[],
        "children":[]
        },
        {
        "key":"Convergence","name":"COMEBACK",
        "props":[
            {"name":"TIMESTEPMIN","type":"number","values":[1.0e-5],"min":0,"max":1.0e-3,"step":1.0e-7,"visible":true},
            {"name":"TIMESTEP,UPTIME,TIMESTEPMAX","type":"string","values":["1,3600,8"],"visible":true}
        ],
        "children":[]
        },
        {
        "key":"Convergence","name":"NOCOMEBACK",
        "props":[
            {"name":"TIMESTEP,UPTIME(1)","type":"string","values":["4,20"],"visible":true},
            {"name":"TIMESTEP,UPTIME(2)","type":"string","values":["20,3600"],"visible":true}
        ],
        "children":[]
        },
        {
        "key":"outputs","name":"PRINT",
        "props":[
        {"type":"number","name":"PRINTDEPL Print the increment of displacement or of temperature","values":[0],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1}},
        {"type":"number","name":"PRINTDEPL Tstart","values":[0],"min":0,"max":1000,"step":1,"visible":true},
        {"type":"number","name":"PRINTTMPRT Print the temperature in the beam fibers","values":[0],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1}},
        {"type":"number","name":"PRINTVELAC Print velocity and acceleration","values":[0],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1}},
        {"type":"number","name":"PRINTFHE Print out of balance forces","values":[0],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1}},
        {"type":"number","name":"PRINTFHE Tstart","values":[0],"min":0,"max":1000,"step":1,"visible":true},
        {"type":"number","name":"PRINTREACT Print the reactions","values":[1],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1}},
        {"type":"number","name":"PRINTMN Print the internal forces in beam elements","values":[1],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1}},
        {"type":"number","name":"PRNEIBEAM Print the stiffness EI in beam elements","values":[0],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1}},
        {"type":"number","name":"PRINTSHELL Print the stresses in shell elements","values":[0],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1}},
        {"type":"number","name":"PRNNXSHELL Print the membrane forces in shell elements","values":[0],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1}},
        {"type":"number","name":"PRNMXSHELL Print the bending moments in shell elements","values":[0],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1}},
        {"type":"number","name":"PRNEASHELL Print the membrane stiffness EA in shell elements","values":[0],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1}},
        {"type":"number","name":"PRNEISHELL Print the membrane stiffness EI in shell elements","values":[0],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1}}
        ],
        "children":[]
        }
    ]},
    {
    "key":"Problem Type","name":"Structural 3D",
    "props":[],
    "children":[
    ]}
]}
"""


#{"name":"Br1","key":"","props":[],"children":[]}

contextDBstring="""
{
"name":"allContextMenus",
"key":"",
"props":[],
"children":[
    {
    "key":"Shape","name":"Point",
    "props":[],
    "children":[
        {
        "key":"Problem Type","name":"Thermal 2D",
        "props":[],
        "children":[
            {
            "key":"Property Type","name":"Block Constraint",
            "props":[],
            "children":[
                {
                "key":"Temperature Type","name":"-",
                "props":[
                    {"name":"00Temperature","valueLabels":{"FISO":0,"F20":1,"F100":2,"HYDROCARB":3,"HCM":4, "ASTME119":5, "RWS":6,"User-defined":7},"choices":[0,1,2,3,4,5,6,7],"type":"number","values":[0]},
                    {"name":"01File for Temperature","type":"string","values":[""],"visible":false},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"SAME Constraint",
            "props":[ ],
            "children":[
            {
                "key":"SAME Type","name":"-",
                "props":[
                    {"name":"0CTRAV(1)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                    {"ents":{},"pgs":{}
                }],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Torsion Point Constraint",
            "props":[],
            "children":[
                {
                "key":"Temperature Type","name":"-",
                "props":[
                    {"name":"00Block","valueLabels":{"F0":0,"User-defined":1},"choices":[0,1],"type":"number","values":[0]},
                    {"name":"01File for Block function","type":"string","values":[""],"visible":false},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            }
        ]
        },
        {
        "key":"Problem Type","name":"Thermal 3D",
        "props":[],
        "children":[
            {
            "key":"Property Type","name":"Block Constraint",
            "props":[],
            "children":[
                {
                "key":"Temperature Type","name":"-",
                "props":[
                    {"name":"00Temperature","valueLabels":{"FISO":0,"F20":1,"F100":2,"HYDROCARB":3,"HCM":4, "ASTME119":5, "RWS":6,"User-defined":7},"choices":[0,1,2,3,4,5,6,7],"type":"number","values":[0]},
                    {"name":"01File for Temperature","type":"string","values":[""],"visible":false},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"SAME Constraint",
            "props":[],
            "children":[
                {
                "key":"SAME Type","name":"-",
                "props":[
                    {"name":"0CTRAV(1)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                    {"ents":{},"pgs":{}
                }],
                "children":[]
                }
            ]
            }
        ]
        },
        {
        "key":"Problem Type","name":"Structural 2D",
        "props":[],
        "children":[
            {
            "key":"Property Type","name":"Block Constraint",
            "props":[],
            "children":[
                {
                "key":"BL Type","name":"-",
                "props":[
                {"name":"00X","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"01File for X","type":"string","values":[""],"visible":false},
                {"name":"10Y","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"11File for Y","type":"string","values":[""],"visible":false},
                {"name":"20Theta-Z","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"21File for Theta-Z","type":"string","values":[""],"visible":false},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"SAME Constraint",
            "props":[],
            "children":[
                {
                "key":"SAME Type","name":"-",
                "props":[
                {"name":"0X","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"1Y","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"2Theta-Z","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Oblique Support for displacements",
            "props":[],
            "children":[
                {
                "key":"ObliqueDisp Type","name":"-",
                "props":[
                {"name":"0Point2(x,y)","type":"string","values":["0,0"]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Oblique Support for rotations",
            "props":[],
            "children":[
                {
                "key":"ObliqueRot Type","name":"-",
                "props":[
                {"name":"0Point2(x,y)","type":"string","values":["0,0"]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Loads on Node",
            "props":[],
            "children":[
                {
                "key":"Load Function Type","name":"-",
                "props":[
                    {"name":"00Load Function","valueLabels":{"F1":0,"FLOAD":1,"F1PS":2,"F1000PS":3,"User-defined":4},"choices":[0,1,2,3,4],"type":"number","values":[0]},
                    {"name":"01File for Load Function","type":"string","values":[""],"visible":false},
                    {"name":"1X-Force","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"2Y-Force","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"3Z-Moment","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Mass on Node",
            "props":[],
            "children":[
                {
                "key":"Mass Node Type","name":"-",
                "props":[
                {"name":"0Mass1","type":"number","values":[0],"min":0,"max":100,"step":0},
                {"name":"1Mass2","type":"number","values":[0],"min":0,"max":100,"step":0},
                {"name":"2Mass3","type":"number","values":[0],"min":0,"max":100,"step":0},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Spring",
            "props":[],
            "children":[]
            }
        ]},
        {
        "key":"Problem Type","name":"Structural 3D",
        "props":[],
        "children":[
            {
            "key":"Property Type","name":"Block Constraint",
            "props":[],
            "children":[
                {
                "key":"BL Type","name":"-",
                "props":[
                {"name":"00X","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"01File for X","type":"string","values":[""],"visible":false},
                {"name":"10Y","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"11File for Y","type":"string","values":[""],"visible":false},
                {"name":"20Z","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"21File for Z","type":"string","values":[""],"visible":false},
                {"name":"30Theta-X","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"31File for Theta-X","type":"string","values":[""],"visible":false},
                {"name":"40Theta-Y","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"41File for Theta-Y","type":"string","values":[""],"visible":false},
                {"name":"50Theta-Z","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"51File for Theta-Z","type":"string","values":[""],"visible":false},
                {"name":"60W","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"61File for W","type":"string","values":[""],"visible":false},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"SAME Constraint",
            "props":[],
            "children":[
                {
                "key":"SAME Type","name":"-",
                "props":[
                {"name":"0X","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"1Y","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"2Z","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"3Theta-X","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"4Theta-Y","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"5Theta-Z","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"6W","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Oblique Support for displacements",
            "props":[],
            "children":[
                {
                "key":"ObliqueDisp Type","name":"-",
                "props":[
                {"name":"0Point2(x,y,z)","type":"string","values":["0,0,0"]},
                {"name":"0Point3(x,y,z)","type":"string","values":["0,0,0"]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Oblique Support for rotations",
            "props":[],
            "children":[
                {
                "key":"ObliqueRot Type","name":"-",
                "props":[
                {"name":"0Point2(x,y,z)","type":"string","values":["0,0,0"]},
                {"name":"0Point3(x,y,z)","type":"string","values":["0,0,0"]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Loads on Node",
            "props":[],
            "children":[

                {
                "key":"Load Function Type","name":"-",
                "props":[
                    {"name":"00Load Function","valueLabels":{"F1":0,"FLOAD":1,"F1PS":2,"F1000PS":3,"User-defined":4},"choices":[0,1,2,3,4],"type":"number","values":[0]},
                    {"name":"01File for Load Function","type":"string","values":["x.fct"],"visible":false},
                    {"name":"1X-Force","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"2Y-Force","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"3Z-Force","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"4X-Moment","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"5Y-Moment","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"6Z-Moment","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Mass on Node",
            "props":[],
            "children":[
                {
                "key":"Mass Node Type","name":"-",
                "props":[
                {"name":"0Mass1","type":"number","values":[0],"min":0,"max":100,"step":0},
                {"name":"1Mass2","type":"number","values":[0],"min":0,"max":100,"step":0},
                {"name":"2Mass3","type":"number","values":[0],"min":0,"max":100,"step":0},
                {"name":"3Mass4","type":"number","values":[0],"min":0,"max":100,"step":0},
                {"name":"4Mass5","type":"number","values":[0],"min":0,"max":100,"step":0},
                {"name":"5Mass6","type":"number","values":[0],"min":0,"max":100,"step":0},
                {"name":"6Mass7","type":"number","values":[0],"min":0,"max":100,"step":0},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Spring",
            "props":[],
            "children":[]
            }
        ]}
    ]},
    {
    "key":"Shape","name":"Curve",
    "props":[],
    "children":[
        {
        "key":"Problem Type","name":"Thermal 2D",
        "props":[],
        "children":[
            {
            "key":"Property Type","name":"Flux Constraint",
            "props":[],
            "children":[
                {
                "key":"Flux Type","name":"-",
                "props":[
                    {"name":"00Flux","valueLabels":{"HASEMI":0,"LOCAFI":1,"CFD":2,"User-defined":3},"choices":[0,1,2,3],"type":"number","values":[0]},
                    {"name":"01File for Flux","type":"string","values":[""],"visible":false},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Frontier Constraint",
            "props":[],
            "children":[
                {
                "key":"Frontier Type","name":"-",
                "props":[
                    {"name":"00Temperature","valueLabels":{"FISO":0,"F20":1,"HYDROCARB":2,"HCM":3, "ASTME119":4, "RWS":5,"User-defined":6},"choices":[0,1,2,3,4,5,6],"type":"number","values":[0]},
                    {"name":"01File for Temperature","type":"string","values":[""],"visible":false},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Block Constraint",
            "props":[],
            "children":[
                {
                "key":"Temperature Type","name":"-",
                "props":[
                    {"name":"00Temperature","valueLabels":{"FISO":0,"F20":1,"F100":2,"HYDROCARB":3,"HCM":4, "ASTME119":5, "RWS":6,"User-defined":7},"choices":[0,1,2,3,4,5,6,7],"type":"number","values":[0]},
                    {"name":"01File for Temperature","type":"string","values":[""],"visible":false},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"SAME Constraint",
            "props":[],
            "children":[
                {
                "key":"SAME Type","name":"-",
                "props":[
                {"name":"0CTRAV(1)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Void Constraint",
            "props":[],
            "children":[
                {
                "key":"Void Type","name":"-",
                "props":[
                    {"name":"Void number","type":"number","values":[1],"min":0,"max":1,"step":1},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }]
            },
            {
            "key":"Property Type","name":"Void SymAxis Constraint",
            "props":[],
            "children":[
                {
                "key":"Void SymAxis Type","name":"-",
                "props":[
                    {"name":"Void number","type":"number","values":[1],"min":0,"max":1,"step":1},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }]
            },
            {
            "key":"Property Type","name":"Real SymAxis Constraint",
            "props":[],
            "children":[
                {
                "key":"Real SymAxis Type","name":"-",
                "props":[{"ents":{},"pgs":{}}],
                "children":[]
                }]
            }
        ]},
        {
        "key":"Problem Type","name":"Thermal 3D",
        "props":[],
        "children":[
            {
            "key":"Property Type","name":"Block Constraint",
            "props":[],
            "children":[
                {
                "key":"Temperature Type","name":"-",
                "props":[
                    {"name":"00Temperature","valueLabels":{"FISO":0,"F20":1,"F100":2,"HYDROCARB":3,"HCM":4, "ASTME119":5, "RWS":6,"User-defined":7},"choices":[0,1,2,3,4,5,6,7],"type":"number","values":[0]},
                    {"name":"01File for Temperature","type":"string","values":[""],"visible":false},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"SAME Constraint",
            "props":[],
            "children":[
                {
                "key":"SAME Type","name":"-",
                "props":[
                {"name":"0CTRAV(1)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            }
        ]
        },
        {
        "key":"Problem Type","name":"Structural 2D",
        "props":[],
        "children":[
            {
            "key":"Property Type","name":"Block Constraint",
            "props":[],
            "children":[
                {
                "key":"BL Type","name":"-",
                "props":[
                {"name":"00X","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"01File for X","type":"string","values":[""],"visible":false},
                {"name":"10Y","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"11File for Y","type":"string","values":[""],"visible":false},
                {"name":"20Theta-Z","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"21File for Theta-Z","type":"string","values":[""],"visible":false},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"SAME Constraint",
            "props":[],
            "children":[
                {
                "key":"SAME Type","name":"-",
                "props":[
                {"name":"0CTRAV(1)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"1CTRAV(2)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"2CTRAV(3)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Beam Section Type",
            "props":[],
            "children":[
            {
                "key":"Sub-Type","name":"-",
                "props":[
                {"name":"0TEM Filename","type":"string","values":[""]},
                {"name":"1Material Name(s)","type":"string","values":[""]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Relaxation Beam",
            "props":[],
            "children":[
            {
                "key":"Sub-Type","name":"-",
                "props":[
                {"name":"1Node1-Xlocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"2Node1-Ylocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"3Node1-thetaZlocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"4Node2-Xlocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"5Node2-Ylocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"6Node2-thetaZlocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Unif Distr Loads on Beam",
            "props":[],
            "children":[

                {
                "key":"Load Function Type","name":"-",
                "props":[
                    {"name":"00Load Function","valueLabels":{"F1":0,"FLOAD":1,"F1PS":2,"F1000PS":3,"User-defined":4},"choices":[0,1,2,3,4],"type":"number","values":[0]},
                    {"name":"01File for Load Function","type":"string","values":[""],"visible":false},
                    {"name":"1X Pressure","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"2Y Pressure","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Beam Trapezoidal Global Loads",
            "props":[],
            "children":[
                {
                "key":"Load Function Type","name":"-",
                "props":[
                    {"name":"00Load Function","valueLabels":{"F1":0,"FLOAD":1,"F1PS":2,"F1000PS":3,"User-defined":4},"choices":[0,1,2,3,4],"type":"number","values":[0]},
                    {"name":"01File for Load Function","type":"string","values":["y.fct"],"visible":false},
                    {"name":"1X Pressure node1","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"2Y Pressure node1","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"3X Pressure node2","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"4Y Pressure node2","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Beam Trapezoidal Local Loads",
            "props":[],
            "children":[
                {
                "key":"Load Function Type","name":"-",
                "props":[
                    {"name":"00Load Function","valueLabels":{"F1":0,"FLOAD":1,"F1PS":2,"F1000PS":3,"User-defined":4},"choices":[0,1,2,3,4],"type":"number","values":[0]},
                    {"name":"01File for Load Function","type":"string","values":["y.fct"],"visible":false},
                    {"name":"1X Pressure node1","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"2Y Pressure node1","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"3X Pressure node2","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"4Y Pressure node2","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Beam Hydrostatic Loads",
            "props":[],
            "children":[
                {
                "key":"Load Function Type","name":"-",
                "props":[
                    {"name":"00Load Function","valueLabels":{"F0":0,"User-defined":1},"choices":[0,1],"type":"number","values":[0]},
                    {"name":"01File for Load Function","type":"string","values":["hfunc.txt"],"visible":false},
                    {"name":"1Specific weight","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Mass on Beam",
            "props":[],
            "children":[
                {
                "key":"Mass Node Type","name":"-",
                "props":[
                {"name":"0Distributed-Beam-Mass","type":"number","values":[0],"min":0,"max":100,"step":0},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Truss Section Type",
            "props":[],
            "children":[
            {
                "key":"Sub-Type","name":"-",
                "props":[
                {"name":"0Filename","type":"string","values":[""]},
                {"name":"1Cross sectional area","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                {"name":"2Residual Stress","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                {"name":"3Material Name(s)","type":"string","values":[""]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"New Material Definition",
            "props":[],
            "children":[
                {
                "key":"Material Type","name":"NONLOAD BEARING",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"Insulation",
                    "props":[
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]}
                ]},
                {
                "key":"Material Type","name":"ELASTIC MATERIALS",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"ELASTIC",
                    "props":[
                            {"name":"90Young module","type":"number","values":[1.1e10],"min":0,"max":1e12,"step":0},
                            {"name":"9Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"USER_ELAS",
                    "props":[
                            {"name":"90Young module","type":"number","values":[1.1e10],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[4.5e7],"min":0,"max":1e9,"step":0},
                            {"name":"93Compressive strength","type":"number","values":[3e7],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}    
                    ],
                    "children":[]
                    }
                ]},

                {
                "key":"Material Type","name":"CARBON STEEL",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"STEELEC3EN",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[3.55e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Max Temperature","type":"number","values":[1200],"min":0,"max":2000,"step":0},
                            {"name":"94Rate Decrease of Yield strength","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"PSTEELA16",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[2.45e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Max Temperature","type":"number","values":[1200],"min":0,"max":2000,"step":0},
                            {"name":"94Rate Decrease of Yield strength","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"STEELEC2EN",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[5e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Max Temperature","type":"number","values":[1200],"min":0,"max":2000,"step":0},
                            {"name":"94Rate Decrease of Yield strength","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"name":"95Process Fabrication","valueLabels":{"HOTROLLED":0,"COLDFORMED":1},"choices":[0,1],"type":"number","values":[0]},
                            {"name":"96Class Ductibility","valueLabels":{"CLASS_A":0,"CLASS_B":1,"CLASS_C":2},"choices":[0,1,2],"type":"number","values":[0]},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"STEEL_WPB",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[2.45e8],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"STEELSL",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[2.45e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Max Temperature","type":"number","values":[1200],"min":0,"max":2000,"step":0},
                            {"name":"94Rate Decrease of Yield strength","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"name":"95Slenderness","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"name":"96Number of supports","type":"number","values":[3],"min":0,"max":50,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"STEC3PROBA",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[2.45e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Max Temperature","type":"number","values":[1200],"min":0,"max":2000,"step":0},
                            {"name":"94Rate Decrease of Yield strength","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"USER_STEEL",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[2.35e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Max Temperature","type":"number","values":[1200],"min":0,"max":2000,"step":0},
                            {"name":"94Rate Decrease of Yield strength","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    }
                ]},
                {
                "key":"Material Type","name":"STAINLESS STEELS",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"SLS1.4301",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[2.35e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Ultimate tensile strength","type":"number","values":[0],"min":0,"max":2000,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"SLS1.4401",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[2.35e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Ultimate tensile strength","type":"number","values":[0],"min":0,"max":2000,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"SLS1.4404",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[2.35e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Ultimate tensile strength","type":"number","values":[0],"min":0,"max":2000,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"SLS1.4571",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[2.35e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Ultimate tensile strength","type":"number","values":[0],"min":0,"max":2000,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"SLS1.4003",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[2.35e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Ultimate tensile strength","type":"number","values":[0],"min":0,"max":2000,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"SLS1.4462",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[2.35e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Ultimate tensile strength","type":"number","values":[0],"min":0,"max":2000,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"SLS1.4311",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[2.35e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Ultimate tensile strength","type":"number","values":[0],"min":0,"max":2000,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    }
                ]},

                {
                "key":"Material Type","name":"NS CONCRETES",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"SILCO_COLD",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"CALCO_COLD",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"SILCONC_EN",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"92Tensile strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"CALCONC_EN",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"92Tensile strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"SILCON_ETC",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"92Tensile strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"CALCON_ETC",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"92Tensile strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"SILHSC1_EN",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"92Tensile strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"SILHSC2_EN",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"92Tensile strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"SILHSC3_EN",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"92Tensile strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"CALHSC1_EN",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"92Tensile strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"CALHSC2_EN",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"92Tensile strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"CALHSC3_EN",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"92Tensile strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"SILHSC1ETC",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"92Tensile strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"SILHSC2ETC",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"92Tensile strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"SILHSC3ETC",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"92Tensile strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"CALHSC1ETC",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"92Tensile strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"CALHSC2ETC",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"92Tensile strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"CALHSC3ETC",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"92Tensile strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    }
                ]},

                {
                "key":"Material Type","name":"SPECIAL CONCRETES",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"LWCONC_EN",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"92Tensile strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"SILCONC_PR",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"CALCONC_PR",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"CACOPRBWE",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"SICOPRBWE",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"CALCONETCL",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"SILCONETCL",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"USER_CONC",
                    "props":[
                            {"name":"90Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"91Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    }
                ]},
                {
                "key":"Material Type","name":"WOOD",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"USER_CONC",
                    "props":[
                            {"name":"90Young module","type":"number","values":[1e10],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    }
                ]},
                {
                "key":"Material Type","name":"ALUMINIUM",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"AL6061T6C",
                    "props":[
                            {"name":"90f0.2","type":"number","values":[7e10],"min":0,"max":1e12,"step":0},
                            {"name":"91fp","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92e(rupture)","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"AL5083SUP",
                    "props":[
                            {"name":"90f0.2","type":"number","values":[7e10],"min":0,"max":1e12,"step":0},
                            {"name":"91fp","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92e(rupture)","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"AL5083INF",
                    "props":[
                            {"name":"90f0.2","type":"number","values":[7e10],"min":0,"max":1e12,"step":0},
                            {"name":"91fp","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92e(rupture)","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"AL7020SUP",
                    "props":[
                            {"name":"90f0.2","type":"number","values":[7e10],"min":0,"max":1e12,"step":0},
                            {"name":"91fp","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92e(rupture)","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"AL7020INF",
                    "props":[
                            {"name":"90f0.2","type":"number","values":[7e10],"min":0,"max":1e12,"step":0},
                            {"name":"91fp","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92e(rupture)","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    }
                ]},
                {
                "key":"Material Type","name":"OTHERS",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"BILIN",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[2.35e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Slope of hardening branch","type":"number","values":[0],"min":0,"max":2000,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"RAMBOSGOOD",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92lp, limit of proportionality","type":"number","values":[0],"min":0,"max":2000,"step":0},
                            {"name":"93n, exponent of the law","type":"number","values":[0],"min":0,"max":2000,"step":0},
                            {"name":"94k, factor of the law","type":"number","values":[0],"min":0,"max":2000,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    }
                ]}
            ]}
        ]},
        {
        "key":"Problem Type","name":"Structural 3D",
        "props":[],
        "children":[
            {
            "key":"Property Type","name":"Block Constraint",
            "props":[],
            "children":[
                {
                "key":"BL Type","name":"-",
                "props":[
                {"name":"00X","valueLabels":{"NO":0,"F0":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"01File for X","type":"string","values":[""],"visible":false},
                {"name":"10Y","valueLabels":{"NO":0,"F0":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"11File for Y","type":"string","values":[""],"visible":false},
                {"name":"20Z","valueLabels":{"NO":0,"F0":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"21File for Z","type":"string","values":[""],"visible":false},
                {"name":"30Theta-X","valueLabels":{"NO":0,"F0":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"31 File for Theta-X","type":"string","values":[""],"visible":false},
                {"name":"40Theta-Y","valueLabels":{"NO":0,"F0":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"41 File for Theta-Y","type":"string","values":[""],"visible":false},
                {"name":"50Theta-Z","valueLabels":{"NO":0,"F0":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"51 File for Theta-Z","type":"string","values":[""],"visible":false},
                {"name":"60W","valueLabels":{"NO":0,"F0":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"61File for W","type":"string","values":[""],"visible":false},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"SAME Constraint",
            "props":[],
            "children":[
                {
                "key":"SAME Type","name":"-",
                "props":[
                {"name":"0X","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"1Y","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"2Z","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"3Theta-X","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"4Theta-Y","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"5Theta-Z","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"6W","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"New LAX Definition",
            "props":[],
            "children":[
            {
                "key":"Sub-Type","name":"-",
                "props":[
                {"name":"0Check=LAX from local angle, Uncheck=LAX from fix coords","type":"number","values":[1],"choices":[0, 1],"valueLabels":{"NO":0,"YES":1}},
                {"name":"1Rotation angle (deg) of Y' around X'","type":"number","values":[0],"min":-180,"max":180,"step":1,"visible":true},
                {"name":"2Reverse X' axis","type":"number","values":[0],"choices":[0, 1],"visible":true},
                {"name":"4Y'(dx,dy,dz)","type":"string","values":["0,0,0"],"visible":false},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]},
            {
            "key":"Property Type","name":"Beam Section Type",
            "props":[],
            "children":[
            {
                "key":"Sub-Type","name":"-",
                "props":[
                {"name":"0TEM Filename","type":"string","values":[""]},
                {"name":"1Material Name(s)","type":"string","values":[""]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]},
            {
            "key":"Property Type","name":"Beam Section Local Axes",
            "props":[],
            "children":[
            {
                "key":"Sub-Type","name":"-",
                "props":[
                {"name":"0LAX Name","type":"string","values":[""]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]},
            {
            "key":"Property Type","name":"Relaxation Beam",
            "props":[],
            "children":[
            {
                "key":"Sub-Type","name":"-",
                "props":[
                {"name":"01Node1-Xlocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"02Node1-Ylocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"03Node1-Zlocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"04Node1-thetaXlocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"05Node1-thetaYlocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"06Node1-thetaZlocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"07Node1-W","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"08Node2-Xlocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"09Node2-Ylocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"10Node2-Zlocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"11Node2-thetaXlocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"12Node2-thetaYlocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"13Node2-thetaZlocal","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"14Node2-W","type":"number","values":[0],"min":0,"max":1,"step":0.1},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Unif Distr Loads on Beam",
            "props":[],
            "children":[
                {
                "key":"Load Function Type","name":"-",
                "props":[
                    {"name":"00Load Function","valueLabels":{"F1":0,"FLOAD":1,"F1PS":2,"F1000PS":3,"User-defined":4},"choices":[0,1,2,3,4],"type":"number","values":[0]},
                    {"name":"01File for Load Function","type":"string","values":["y.fct"],"visible":false},
                    {"name":"1X Pressure","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"2Y Pressure","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"3Z Pressure","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Beam Trapezoidal Global Loads",
            "props":[],
            "children":[
                {
                "key":"Load Function Type","name":"-",
                "props":[
                    {"name":"00Load Function","valueLabels":{"F1":0,"FLOAD":1,"F1PS":2,"F1000PS":3,"User-defined":4},"choices":[0,1,2,3,4],"type":"number","values":[0]},
                    {"name":"01File for Load Function","type":"string","values":["y.fct"],"visible":false},
                    {"name":"1X Pressure node1","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"2Y Pressure node1","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"3Z Pressure node1","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"4X Pressure node2","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"5Y Pressure node2","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"6Z Pressure node2","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Beam Trapezoidal Local Loads",
            "props":[],
            "children":[
                {
                "key":"Load Function Type","name":"-",
                "props":[
                    {"name":"00Load Function","valueLabels":{"F1":0,"FLOAD":1,"F1PS":2,"F1000PS":3,"User-defined":4},"choices":[0,1,2,3,4],"type":"number","values":[0]},
                    {"name":"01File for Load Function","type":"string","values":["y.fct"],"visible":false},
                    {"name":"1X Pressure node1","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"2Y Pressure node1","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"3Z Pressure node1","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"4X Pressure node2","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"5Y Pressure node2","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"6Z Pressure node2","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Beam Hydrostatic Loads",
            "props":[],
            "children":[
                {
                "key":"Load Function Type","name":"-",
                "props":[
                    {"name":"00Load Function","valueLabels":{"F0":0,"User-defined":1},"choices":[0,1],"type":"number","values":[0]},
                    {"name":"01File for Load Function","type":"string","values":["hfunc.txt"],"visible":false},
                    {"name":"1Specific weight","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Mass on Beam",
            "props":[],
            "children":[
                {
                "key":"Mass Node Type","name":"-",
                "props":[
                {"name":"0Distributed-Beam-Mass","type":"number","values":[0],"min":0,"max":100,"step":0},
                {"name":"1Rotational-Inertia","type":"number","values":[0],"min":0,"max":100,"step":0},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Truss Section Type",
            "props":[],
            "children":[
            {
                "key":"Sub-Type","name":"-",
                "props":[
                {"name":"0Filename","type":"string","values":[""]},
                {"name":"1Cross sectional area","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                {"name":"2Residual Stress","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                {"name":"3Material Name(s)","type":"string","values":[""]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]},
            {
            "key":"Property Type","name":"New Material Definition",
            "props":[],
            "children":[]
            }
        ]}
    ]},
    {"key":"Shape","name":"Surface",
    "props":[],
    "children":[
        {
        "key":"Problem Type","name":"Thermal 2D",
        "props":[],
        "children":[
            {
            "key":"Property Type","name":"Surface Material",
            "props":[],
            "children":[
            {
                "key":"Sub-Type","name":"-",
                "props":[
                {"name":"1Material Name(s)","type":"string","values":[""]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]},
            {
            "key":"Property Type","name":"SAME Constraint",
            "props":[],
            "children":[
                {
                "key":"SAME Type","name":"-",
                "props":[
                {"name":"0CTRAV(1)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"New Material Definition",
            "props":[],
            "children":[
                {
                "key":"Material Type","name":"Insulations",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"Insulation",
                    "props":[
                            {"name":"HIDDEN torsname","type":"string","values":["INSULATION"]},
                            {"name":"1Thermal conductivity","type":"number","values":[2],"min":0,"max":100,"step":0},
                            {"name":"2Specific heat","type":"number","values":[900],"min":0,"max":1000,"step":0},
                            {"name":"3Volumic mass","type":"number","values":[40],"min":0,"max":1,"step":0},
                            {"name":"4Water Content","type":"number","values":[5],"min":0,"max":100,"step":0},
                            {"name":"5Temperature when evaporation starts","type":"number","values":[100],"min":0,"max":200,"step":0},
                            {"name":"6Temperature when evaporation stops","type":"number","values":[110],"min":0,"max":200,"step":0},
                            {"name":"7Convection coeff hot","type":"number","values":[25],"min":0,"max":100,"step":0},
                            {"name":"8Convection coeff cold","type":"number","values":[4],"min":0,"max":100,"step":0},
                            {"name":"90Relative emission","type":"number","values":[0.8],"min":0,"max":1,"step":0},
                            {"name":"91Young module","type":"number","values":[1.2e10],"min":0,"max":1e12,"step":0},
                            {"name":"92Poisson coefficient","type":"number","values":[0.2],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]},
                    {
                    "key":"Material Sub-category","name":"SFRM_Proba",
                    "props":[
                            {"name":"HIDDEN torsname","type":"string","values":["INSULATION"]},
                            {"name":"1Epsilon Thermal conductivity","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"name":"2Epsilon Specific heat","type":"number","values":[0],"min":0,"max":1000,"step":0},
                            {"name":"3Epsilon Volumic mass","type":"number","values":[0],"min":0,"max":1,"step":0},
                            {"name":"4Water Content","type":"number","values":[5],"min":0,"max":100,"step":0},
                            {"name":"5Temperature when evaporation starts","type":"number","values":[100],"min":0,"max":200,"step":0},
                            {"name":"6Temperature when evaporation stops","type":"number","values":[110],"min":0,"max":200,"step":0},
                            {"name":"7Convection coeff hot","type":"number","values":[25],"min":0,"max":100,"step":0},
                            {"name":"8Convection coeff cold","type":"number","values":[4],"min":0,"max":100,"step":0},
                            {"name":"90Relative emission","type":"number","values":[0.8],"min":0,"max":1,"step":0},
                            {"name":"91Young module","type":"number","values":[1.2e10],"min":0,"max":1e12,"step":0},
                            {"name":"92Poisson coefficient","type":"number","values":[0.2],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]}
                ]},
                {
                "key":"Material Type","name":"Gypsum",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"C_Gypsum",
                    "props":[
                            {"name":"HIDDEN torsname","type":"string","values":["INSULATION"]},
                            {"name":"1Convection coeff hot","type":"number","values":[25],"min":0,"max":100,"step":0},
                            {"name":"2Convection coeff cold","type":"number","values":[4],"min":0,"max":100,"step":0},
                            {"name":"3Relative emission","type":"number","values":[0.7],"min":0,"max":1,"step":0},
                            {"name":"90Young module","type":"number","values":[1.2e10],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.2],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]},
                    {
                    "key":"Material Sub-category","name":"X_Gypsum",
                    "props":[
                            {"name":"HIDDEN torsname","type":"string","values":["INSULATION"]},
                            {"name":"1Convection coeff hot","type":"number","values":[25],"min":0,"max":100,"step":0},
                            {"name":"2Convection coeff cold","type":"number","values":[4],"min":0,"max":100,"step":0},
                            {"name":"3Relative emission","type":"number","values":[0.7],"min":0,"max":1,"step":0},
                            {"name":"90Young module","type":"number","values":[1.2e10],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.2],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]}
                ]},
                {
                "key":"Material Type","name":"Concrete",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"Calconc_En",
                    "props":[
                            {"name":"HIDDEN torsname","type":"string","values":["ELASTIC"]},
                            {"name":"1Specific mass","type":"number","values":[2300],"min":0,"max":10000,"step":0},
                            {"name":"2Moisture content","type":"number","values":[34.5],"min":0,"max":250,"step":0},
                            {"name":"3Convection coeff hot","type":"number","values":[25],"min":0,"max":100,"step":0},
                            {"name":"4Convection coeff cold","type":"number","values":[4],"min":0,"max":100,"step":0},
                            {"name":"5Relative emission","type":"number","values":[0.7],"min":0,"max":1,"step":0},
                            {"name":"6Parameter of thermal conductivity","type":"number","values":[0.5],"min":0,"max":1,"step":0},
                            {"name":"90Young module","type":"number","values":[1.2e10],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.2],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"Silconc_En",
                    "props":[
                            {"name":"HIDDEN torsname","type":"string","values":["ELASTIC"]},
                            {"name":"1Specific mass","type":"number","values":[2300],"min":0,"max":10000,"step":0},
                            {"name":"2Moisture content","type":"number","values":[34.5],"min":0,"max":250,"step":0},
                            {"name":"3Convection coeff hot","type":"number","values":[25],"min":0,"max":100,"step":0},
                            {"name":"4Convection coeff cold","type":"number","values":[4],"min":0,"max":100,"step":0},
                            {"name":"5Relative emission","type":"number","values":[0.7],"min":0,"max":1,"step":0},
                            {"name":"6Parameter of thermal conductivity","type":"number","values":[0.5],"min":0,"max":1,"step":0},
                            {"name":"90Young module","type":"number","values":[1.2e10],"min":0,"max":1e12,"step":0},
                            {"name":"9Poisson coefficient","type":"number","values":[0.2],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"Calconc_Pr",
                    "props":[
                            {"name":"HIDDEN torsname","type":"string","values":["ELASTIC"]},
                            {"name":"1Specific mass","type":"number","values":[2300],"min":0,"max":10000,"step":0},
                            {"name":"2Moisture content","type":"number","values":[24.5],"min":0,"max":250,"step":0},
                            {"name":"3Convection coeff hot","type":"number","values":[25],"min":0,"max":100,"step":0},
                            {"name":"4Convection coeff cold","type":"number","values":[4],"min":0,"max":100,"step":0},
                            {"name":"5Relative emission","type":"number","values":[0.7],"min":0,"max":1,"step":0},
                            {"name":"6Parameter of thermal conductivity","type":"number","values":[0.5],"min":0,"max":1,"step":0},
                            {"name":"90Young module","type":"number","values":[1.2e10],"min":0,"max":1e12,"step":0},
                            {"name":"9Poisson coefficient","type":"number","values":[0.2],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"Silconc_Pr",
                    "props":[
                            {"name":"HIDDEN torsname","type":"string","values":["ELASTIC"]},
                            {"name":"1Specific mass","type":"number","values":[2300],"min":0,"max":10000,"step":0},
                            {"name":"2Moisture content","type":"number","values":[34.5],"min":0,"max":250,"step":0},
                            {"name":"3Convection coeff hot","type":"number","values":[25],"min":0,"max":100,"step":0},
                            {"name":"4Convection coeff cold","type":"number","values":[4],"min":0,"max":100,"step":0},
                            {"name":"5Relative emission","type":"number","values":[0.7],"min":0,"max":1,"step":0},
                            {"name":"6Parameter of thermal conductivity","type":"number","values":[0.5],"min":0,"max":1,"step":0},
                            {"name":"90Young module","type":"number","values":[1.2e10],"min":0,"max":1e12,"step":0},
                            {"name":"9Poisson coefficient","type":"number","values":[0.2],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"Concen2020",
                    "props":[
                            {"name":"HIDDEN torsname","type":"string","values":["ELASTIC"]},
                            {"name":"1Specific Mass (including moisture)","type":"number","values":[2300],"min":0,"max":10000,"step":0},
                            {"name":"2Moisture content","type":"number","values":[34.5],"min":0,"max":250,"step":0},
                            {"name":"3Convection coeff hot","type":"number","values":[25],"min":0,"max":100,"step":0},
                            {"name":"4Convection coeff cold","type":"number","values":[4],"min":0,"max":100,"step":0},
                            {"name":"5Relative emission","type":"number","values":[0.7],"min":0,"max":1,"step":0},
                            {"name":"90Young module","type":"number","values":[1.2e10],"min":0,"max":1e12,"step":0},
                            {"name":"9Poisson coefficient","type":"number","values":[0.2],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"Lwconc_En",
                    "props":[
                            {"name":"HIDDEN torsname","type":"string","values":["ELASTIC"]},
                            {"name":"1Mass (including moisture)","type":"number","values":[2300],"min":0,"max":10000,"step":0},
                            {"name":"2Moisture content","type":"number","values":[24.5],"min":0,"max":250,"step":0},
                            {"name":"3Convection coeff hot","type":"number","values":[25],"min":0,"max":100,"step":0},
                            {"name":"4Convection coeff cold","type":"number","values":[4],"min":0,"max":100,"step":0},
                            {"name":"5Relative emission","type":"number","values":[0.7],"min":0,"max":1,"step":0},
                            {"name":"90Young module","type":"number","values":[1.2e10],"min":0,"max":1e12,"step":0},
                            {"name":"9Poisson coefficient","type":"number","values":[0.2],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    }
                ]},
                {
                "key":"Material Type","name":"Metal",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"Steelec3en",
                    "props":[
                            {"name":"HIDDEN torsname","type":"string","values":["ELASTIC"]},
                            {"name":"1Convection coeff hot","type":"number","values":[25],"min":0,"max":100,"step":0},
                            {"name":"2Convection coeff cold","type":"number","values":[4],"min":0,"max":100,"step":0},
                            {"name":"3Relative emission","type":"number","values":[0.7],"min":0,"max":1,"step":0},
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"9Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"Steelec2en",
                    "props":[
                            {"name":"HIDDEN torsname","type":"string","values":["ELASTIC"]},
                            {"name":"1Convection coeff hot","type":"number","values":[25],"min":0,"max":100,"step":0},
                            {"name":"2Convection coeff cold","type":"number","values":[4],"min":0,"max":100,"step":0},
                            {"name":"3Relative emission","type":"number","values":[0.7],"min":0,"max":1,"step":0},
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"9Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"Galvasteel",
                    "props":[
                            {"name":"HIDDEN torsname","type":"string","values":["ELASTIC"]},
                            {"name":"1Convection coeff hot","type":"number","values":[25],"min":0,"max":100,"step":0},
                            {"name":"2Convection coeff cold","type":"number","values":[4],"min":0,"max":100,"step":0},
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"9Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"Stainless Steels",
                    "props":[
                            {"name":"HIDDEN torsname","type":"string","values":["ELASTIC"]},
                            {"name":"1Convection coeff hot","type":"number","values":[25],"min":0,"max":100,"step":0},
                            {"name":"2Convection coeff cold","type":"number","values":[4],"min":0,"max":100,"step":0},
                            {"name":"3Relative emission","type":"number","values":[0.4],"min":0,"max":1,"step":0},
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"9Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"Aluminum",
                    "props":[
                            {"name":"HIDDEN torsname","type":"string","values":["ELASTIC"]},
                            {"name":"1Convection coeff hot","type":"number","values":[25],"min":0,"max":100,"step":0},
                            {"name":"2Convection coeff cold","type":"number","values":[4],"min":0,"max":100,"step":0},
                            {"name":"3Relative emission","type":"number","values":[0.7],"min":0,"max":1,"step":0},
                            {"name":"90Young module","type":"number","values":[7e10],"min":0,"max":1e12,"step":0},
                            {"name":"9Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    }
                ]},
                {
                "key":"Material Type","name":"Wood",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"WoodEC5",
                    "props":[
                            {"name":"HIDDEN torsname","type":"string","values":["ELASTIC"]},
                            {"name":"1Specific Mass (including moisture)","type":"number","values":[410],"min":0,"max":10000,"step":0},
                            {"name":"2Moisture content","type":"number","values":[12],"min":0,"max":250,"step":0},
                            {"name":"3Convection coeff hot","type":"number","values":[25],"min":0,"max":100,"step":0},
                            {"name":"4Convection coeff cold","type":"number","values":[4],"min":0,"max":100,"step":0},
                            {"name":"5Relative emission","type":"number","values":[0.8],"min":0,"max":1,"step":0},
                            {"name":"6Ratio of Train Transv. conduct.","type":"number","values":[2],"min":0,"max":1,"step":0},
                            {"name":"7Direction of the grain X-coord","type":"number","values":[0],"min":0,"max":1,"step":0},
                            {"name":"8Direction of the grain Y-coord","type":"number","values":[0],"min":0,"max":1,"step":0},
                            {"name":"9Direction of the grain Z-coord","type":"number","values":[1],"min":0,"max":1,"step":0},
                            {"name":"91Young module","type":"number","values":[1e10],"min":0,"max":1e12,"step":0},
                            {"name":"92Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    }
                ]},
                {
                "key":"Material Type","name":"Generic",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"Generic",
                    "props":[
                            {"name":"HIDDEN torsname","type":"string","values":["ELASTIC"]},
                            {"name":"1Property1","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"name":"2Property2","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"name":"3Property3","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"name":"4Property4","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"name":"5Property5","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"name":"6Property6","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"name":"7Property7","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"name":"8Property8","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"9Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    }
                ]},
                {
                "key":"Material Type","name":"User-defined",
                "props":[
                        {"name":"HIDDEN torsname","type":"string","values":["ELASTIC"]},
                        {"name":"0Filename","type":"string","values":[""]},
                        {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                        {"name":"9Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                        {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]}
        ]},
        {
        "key":"Problem Type","name":"Thermal 3D",
        "props":[],
        "children":[
            {
            "key":"Property Type","name":"Flux Constraint",
            "props":[],
            "children":[
                {
                "key":"Flux Type","name":"-",
                "props":[
                    {"name":"00Flux","valueLabels":{"HASEMI":0,"LOCAFI":1,"CFD":2,"User-defined":3},"choices":[0,1,2,3],"type":"number","values":[0]},
                    {"name":"01File for Flux","type":"string","values":[""],"visible":false},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Frontier Constraint",
            "props":[],
            "children":[
                {
                "key":"Frontier Type","name":"-",
                "props":[
                    {"name":"00Temperature","valueLabels":{"FISO":0,"F20":1,"HYDROCARB":2,"HCM":3, "ASTME119":4, "RWS":5,"User-defined":6},"choices":[0,1,2,3,4,5,6],"type":"number","values":[0]},
                    {"name":"01File for Temperature","type":"string","values":[""],"visible":false},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"SAME Constraint",
            "props":[],
            "children":[
                {
                "key":"SAME Type","name":"-",
                "props":[
                {"name":"0CTRAV(1)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Block Constraint",
            "props":[],
            "children":[
                {
                "key":"Temperature Type","name":"-",
                "props":[
                    {"name":"00Temperature","valueLabels":{"FISO":0,"F20":1,"F100":2,"HYDROCARB":3,"HCM":4, "ASTME119":5, "RWS":6},"choices":[0,1,2,3,4,5,6],"type":"number","values":[0]},
                    {"name":"01File for Temperature","type":"string","values":[""],"visible":false},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            }
        ]},
        {
        "key":"Problem Type","name":"Structural 2D",
        "props":[],
        "children":[
            {
            "key":"Property Type","name":"Block Constraint",
            "props":[],
            "children":[
                {
                "key":"BL Type","name":"-",
                "props":[
                {"name":"00X","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"01File for X","type":"string","values":[""],"visible":false},
                {"name":"10Y","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"11File for Y","type":"string","values":[""],"visible":false},
                {"name":"20Theta-Z","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"21File for Theta-Z","type":"string","values":[""],"visible":false},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"SAME Constraint",
            "props":[],
            "children":[
                {
                "key":"SAME Type","name":"-",
                "props":[
                {"name":"0CTRAV(1)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"1CTRAV(2)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"2CTRAV(3)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"New Material Definition",
            "props":[],
            "children":[
                {
                "key":"Material Type","name":"CARBON STEEL",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"STEELEC32D",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[2.45e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Max Temperature","type":"number","values":[1200],"min":0,"max":2000,"step":0},
                            {"name":"94Rate Decrease of Yield strength","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"STEELEC3PS",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[2.45e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Max Temperature","type":"number","values":[1200],"min":0,"max":2000,"step":0},
                            {"name":"94Rate Decrease of Yield strength","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    }
                ]},
                {
                "key":"Material Type","name":"NS CONCRETES",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"SILCOETC2D",
                    "props":[
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"93Tension strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"name":"94Strain at Peak Stress","type":"number","values":[0.0025],"min":0,"max":2000,"step":0},
                            {"name":"95Dilatancy","type":"number","values":[0.25],"min":0,"max":2000,"step":0},
                            {"name":"96Compressive Ductibility","type":"number","values":[0.19],"min":0,"max":2000,"step":0},
                            {"name":"97Compressive Damage Peak Stress","type":"number","values":[0.3],"min":0,"max":2000,"step":0},
                            {"name":"98Tension Ductibility","type":"number","values":[400],"min":0,"max":2000,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"CALCOETC2D",
                    "props":[
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"93Tension strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"name":"94Strain at Peak Stress","type":"number","values":[0.0025],"min":0,"max":2000,"step":0},
                            {"name":"95Dilatancy","type":"number","values":[0.25],"min":0,"max":2000,"step":0},
                            {"name":"96Compressive Ductibility","type":"number","values":[0.19],"min":0,"max":2000,"step":0},
                            {"name":"97Compressive Damage Peak Stress","type":"number","values":[0.3],"min":0,"max":2000,"step":0},
                            {"name":"98Tension Ductibility","type":"number","values":[400],"min":0,"max":2000,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    }
                ]},
                {
                "key":"Material Type","name":"SPECIAL CONCRETES",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"LWCONC2D",
                    "props":[
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"93Tension strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    }
                ]}
            ]}
        ]},
        {
        "key":"Problem Type","name":"Structural 3D",
        "props":[],
        "children":[
            {
            "key":"Property Type","name":"Block Constraint",
            "props":[],
            "children":[
                {
                "key":"BL Type","name":"-",
                "props":[
                {"name":"00X","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"01File for X","type":"string","values":[""],"visible":false},
                {"name":"10Y","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"11File for Y","type":"string","values":[""],"visible":false},
                {"name":"20Z","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"21File for Z","type":"string","values":[""],"visible":false},
                {"name":"30Theta-X","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"31File for Theta-X","type":"string","values":[""],"visible":false},
                {"name":"40Theta-Y","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"41File for Theta-Y","type":"string","values":[""],"visible":false},
                {"name":"50Theta-Z","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"51File for Theta-Z","type":"string","values":[""],"visible":false},
                {"name":"60W","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"61File for W","type":"string","values":[""],"visible":false},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"SAME Constraint",
            "props":[],
            "children":[
                {
                "key":"SAME Type","name":"-",
                "props":[
                {"name":"0CTRAV(1)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"1CTRAV(2)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"2CTRAV(3)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"3CTRAV(1)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"4CTRAV(2)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"5CTRAV(3)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"6CTRAV(3)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Loads on Shell",
            "props":[],
            "children":[
                {
                "key":"Load Function Type","name":"-",
                "props":[
                    {"name":"00Load Function","valueLabels":{"F1":0,"FLOAD":1,"F1PS":2,"F1000PS":3,"User-defined":4},"choices":[0,1,2,3,4],"type":"number","values":[0]},
                    {"name":"01File for Load Function","type":"string","values":[""],"visible":false},
                    {"name":"1X Pressure","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"2Y Pressure","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"name":"3Z Pressure","type":"number","values":[0],"min":0,"max":100,"step":0},
                    {"ents":{},"pgs":{}}
                    ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Mass on Shell",
            "props":[],
            "children":[
                {
                "key":"Mass Node Type","name":"-",
                "props":[
                {"name":"0Distributed-Shell-Mass","type":"number","values":[0],"min":0,"max":100,"step":0},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Shell Material",
            "props":[],
            "children":[
            {
                "key":"Sub-Type","name":"-",
                "props":[
                {"name":"0Filename","type":"string","values":[""]},
                {"name":"1Thickness","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"2Node level Z0","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"3Material Name(s)","type":"string","values":[""]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]},
            {
            "key":"Property Type","name":"Shell Rebar",
            "props":[],
            "children":[
            {
                "key":"Sub-Type","name":"-",
                "props":[
                {"name":"0Material Name(s)","type":"string","values":[""]},
                {"name":"1Section(s)","type":"string","values":[""]},
                {"name":"2Level(s)","type":"string","values":[""]},
                {"name":"4Angle(s)","type":"string","values":[""]},
                {"name":"5Normal-X(s)","type":"string","values":[""]},
                {"name":"6Normal-Y(s)","type":"string","values":[""]},
                {"name":"7Normal-Z(s)","type":"string","values":[""]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]},
            {
            "key":"Property Type","name":"New Material Definition",
            "props":[],
            "children":[]
            },
            {
            "key":"Property Type","name":"New Rebar Material Definition",
            "props":[],
            "children":[]
            }
        ]}
    ]},
    {"key":"Shape","name":"Volume",
    "props":[],
    "children":[
        {
        "key":"Problem Type","name":"Thermal 3D",
        "props":[],
        "children":[
            {
            "key":"Property Type","name":"SAME Constraint",
            "props":[],
            "children":[
                {
                "key":"SAME Type","name":"-",
                "props":[
                {"name":"0CTRAV(1)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Volume Material",
            "props":[],
            "children":[
            {
                "key":"Sub-Type","name":"-",
                "props":[
                {"name":"1Material Name(s)","type":"string","values":[""]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]},
            {
            "key":"Property Type","name":"New Material Definition",
            "props":[],
            "children":[]
            }
        ]},
        {
        "key":"Problem Type","name":"Structural 3D",
        "props":[],
        "children":[
            {
            "key":"Property Type","name":"Block Constraint",
            "props":[],
            "children":[
                {
                "key":"BL Type","name":"-",
                "props":[
                {"name":"00X","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"01File for X","type":"string","values":[""],"visible":false},
                {"name":"10Y","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"11File for Y","type":"string","values":[""],"visible":false},
                {"name":"20Z","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"21File for Z","type":"string","values":[""],"visible":false},
                {"name":"30Theta-X","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"31File for Theta-X","type":"string","values":[""],"visible":false},
                {"name":"40Theta-Y","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"41File for Theta-Y","type":"string","values":[""],"visible":false},
                {"name":"50Theta-Z","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"51File for Theta-Z","type":"string","values":[""],"visible":false},
                {"name":"60W","valueLabels":{"NO":0,"F0":1,"User-defined":2},"choices":[0,1,2],"type":"number","values":[0]},
                {"name":"61File for W","type":"string","values":[""],"visible":false},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"SAME Constraint",
            "props":[],
            "children":[
                {
                "key":"SAME Type","name":"-",
                "props":[
                {"name":"0CTRAV(1)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"1CTRAV(2)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"2CTRAV(3)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"3CTRAV(4)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"4CTRAV(5)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"5CTRAV(6)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"name":"6CTRAV(7)","valueLabels":{"NO":0,"YES":1},"choices":[0,1],"type":"number","values":[0]},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]
            },
            {
            "key":"Property Type","name":"Solid Material",
            "props":[],
            "children":[
            {
                "key":"Sub-Type","name":"-",
                "props":[
                {"name":"0Filename","type":"string","values":[""]},
                {"name":"1Material Name(s)","type":"string","values":[""]},
                {"name":"2Res1","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"3Res2","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"name":"4Res3","type":"number","values":[0],"min":0,"max":1,"step":0},
                {"ents":{},"pgs":{}}
                ],
                "children":[]
                }
            ]},
            {
            "key":"Property Type","name":"New Material Definition",
            "props":[],
            "children":[
                {
                "key":"Material Type","name":"CARBON STEEL",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"STEELEC23D",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[2.45e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Max Temperature","type":"number","values":[1200],"min":0,"max":2000,"step":0},
                            {"name":"94Rate Decrease of Yield strength","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"STEELEC33D",
                    "props":[
                            {"name":"90Young module","type":"number","values":[2.1e11],"min":0,"max":1e12,"step":0},
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Yield strength","type":"number","values":[2.45e8],"min":0,"max":1e10,"step":0},
                            {"name":"93Max Temperature","type":"number","values":[1200],"min":0,"max":2000,"step":0},
                            {"name":"94Rate Decrease of Yield strength","type":"number","values":[0],"min":0,"max":100,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    }
                ]},
                {
                "key":"Material Type","name":"NS CONCRETES",
                "props":[],
                "children":[
                    {
                    "key":"Material Sub-category","name":"SILCOETC3D",
                    "props":[
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"93Tension strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"name":"94Strain at Peak Stress","type":"number","values":[0.0025],"min":0,"max":2000,"step":0},
                            {"name":"95Dilatancy","type":"number","values":[0.25],"min":0,"max":2000,"step":0},
                            {"name":"96Compressive Ductibility","type":"number","values":[0.19],"min":0,"max":2000,"step":0},
                            {"name":"97Compressive Damage Peak Stress","type":"number","values":[0.3],"min":0,"max":2000,"step":0},
                            {"name":"98Tension Ductibility","type":"number","values":[400],"min":0,"max":2000,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    },
                    {
                    "key":"Material Sub-category","name":"CALCOETC3D",
                    "props":[
                            {"name":"91Poisson coefficient","type":"number","values":[0.3],"min":0,"max":1,"step":0},
                            {"name":"92Compressive strength","type":"number","values":[3e7],"min":0,"max":1e10,"step":0},
                            {"name":"93Tension strength","type":"number","values":[0],"min":0,"max":1e10,"step":0},
                            {"name":"94Strain at Peak Stress","type":"number","values":[0.0025],"min":0,"max":2000,"step":0},
                            {"name":"95Dilatancy","type":"number","values":[0.25],"min":0,"max":2000,"step":0},
                            {"name":"96Compressive Ductibility","type":"number","values":[0.19],"min":0,"max":2000,"step":0},
                            {"name":"97Compressive Damage Peak Stress","type":"number","values":[0.3],"min":0,"max":2000,"step":0},
                            {"name":"98Tension Ductibility","type":"number","values":[400],"min":0,"max":2000,"step":0},
                            {"ents":{},"pgs":{}}
                    ],
                    "children":[]
                    }
                ]}
            ]}
        ]}
    ]}
]}

"""

inspectDBstring="""
{
"name":"inspect",
"props":[],
"children":[
    {
    "key":"Problem Type","name":"Thermal 2D",
            "props":[
            {"type":"string","name":"0View materials","values":["inspect materials"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"1View flux","values":["inspect fluxes"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"2View frontiers","values":["inspect frontiers"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"3View blocks","values":["inspect blocks"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"4View torsion point","values":["inspect tblocks"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"5View voids and symvoids","values":["inspect voids"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"6View real syms","values":["inspect realsym"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"7View same","values":["inspect same"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"8Clean","values":["inspect clean"],"attributes":{"Macro":"Action", "Aspect":"Button"}}
            ],
            "children":[]
    },
    {
    "key":"Problem Type","name":"Thermal 3D",
            "props":[
            {"type":"string","name":"0View materials","values":["inspect materials"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"1View flux","values":["inspect fluxes"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"2View frontiers","values":["inspect frontiers"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"3View blocks","values":["inspect blocks"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"4View same","values":["inspect same"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"5Clean","values":["inspect clean"],"attributes":{"Macro":"Action", "Aspect":"Button"}}
            ],
            "children":[]
    },
    {
    "key":"Problem Type","name":"Structural 2D",
            "props":[
            {"type":"string","name":"0View materials","values":["inspect materials"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"1View blocks","values":["inspect blocks"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"2View same","values":["inspect same"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"3View loads","values":["inspect loads"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"4View relax","values":["inspect relax"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"5View mass","values":["inspect mass"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"6Clean","values":["inspect clean"],"attributes":{"Macro":"Action", "Aspect":"Button"}}
            ],
            "children":[]
    },
    {
    "key":"Problem Type","name":"Structural 3D",
            "props":[
            {"type":"string","name":"0View materials","values":["inspect materials"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"1View local axes","values":["inspect lax"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"2View blocks","values":["inspect blocks"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"3View same","values":["inspect same"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"4View loads","values":["inspect loads"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"5View relax","values":["inspect relax"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"6View mass","values":["inspect mass"],"attributes":{"Macro":"Action", "Aspect":"Button"}},
            {"type":"string","name":"7Clean","values":["inspect clean"],"attributes":{"Macro":"Action", "Aspect":"Button"}}
            ],
            "children":[]
    }
]
}
"""

# {
# "name":"",
# "props":[],
# "children":[]
# }

print(sys.argv)

myapp=Myapp()

if not myapp.nopopup:
    gmsh.fltk.initialize()
    while myapp.eventLoop():
        pass
else:
    gmsh.logger.write("Run G4S in Batch mode", level="info")
    tmpfiles2=[k for k in os.listdir(myapp.dir) if (re.search('.g4s$',k)!=None)]
    #
    if(tmpfiles2!=[]):
        if(len(tmpfiles2)==1):
            myapp.g4sfile=os.path.join(myapp.dir,tmpfiles2[0])
            gmsh.logger.write("Ok, found a single G4S file, "+os.path.basename(myapp.g4sfile)+" : use it for batch mode.", level="info")
            myapp.getG4sJson(myapp.g4sfile) # if existing DB in input director
            #
            tmpfiles=[k for k in os.listdir(myapp.dir) if (re.search('.geo$',k)!=None)]
            if(tmpfiles!=[]):
                gmsh.logger.write("Ok, found the following GEO files, process them in batch mode:\n"+str(tmpfiles), level="info")
                #
                for gfile in tmpfiles:
                    gmsh.open(os.path.join(myapp.dir,gfile))
                    myapp.INfile=gfile.replace(".geo",".IN")
                    pattern=re.compile("[0-9]")
                    ndims=int(re.search(pattern, myapp.pbType).group(0))
                    gmsh.model.geo.synchronize()
                    #
                    if(ndims==2):
                        gmsh.model.mesh.generate(2)
                    if(ndims==3):
                        gmsh.model.mesh.generate(3)
                    #
                    myapp.createIN()
        #
        else:
            msg="-- Batch mode: Too many G4S files in the directory - keep only one --"
            gmsh.logger.write(msg+"\n", level="error")
    #
    else:
        msg="-- Batch mode: No G4S file in the directory - need one --"
        gmsh.logger.write(msg+"\n", level="error")


    #self.INfile=gfile.replace(".geo",".IN")

gmsh.finalize()
