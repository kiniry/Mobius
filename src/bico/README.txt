1. To unify versions of BCEL this info is using bcel.jar provided by 
ESCTools project. Soon it will use the Mobius PVE plugin of 
bcel 5.2
a) this step by step install assume that umbra is installed or
b) second option is copy bcel-5.2.jar to YOURLOCATION

2. Checkout->Check out as a project configured using the new project wizard->finish
3. Java project->Next->Project name:bico->Finish

There will be errors in project to deal with them we must provide bcel.jar
4. bico->properieties->java build path->
a) add jars -> ESC/Tools-> Utils -> BCEL ->org.apache.bcel_5.2.0
b) add external jars->YOURLOCATION
->bcel.jar->ok->ok

5. While executing if you want to work on ready examples - 
check if Addition.class and/or factorial.class are there 
in your bico/test (programs shows default path on console;
you can run program with 1 argument - path[to change default]
or "help" to view brief info on console) - 
sometimes I must put them manually from svn. Looks like Eclipse 
sometimes removes "orphane" .class files.


6. To compile the produced file Bico<Name of Implem>.v in Coq you must first compile
bicolano if you use bico with list (ImplemProgramWithList.v) or 
with maps (ImplemProgramWithMap.v). Bicolano must be in the LoadPath
of bicos'Program generated vernacular file.
   
The generation is now done compatible with what was discussed
in the Mobius Tools mailing list.

7. To compile bico as an independent jar file (to be run with the command
'java -jar bico.jar'), go into the bico directory and type in 'make'.
If it doesn't find bcel as a part of the umbra package you can specify its
absolute path in the makefile.
	