1. To unify versions of BCEL this info is using bcel.jar provided by umbra
a) this step by step install assume that umbra is installed or
b) second option is copy umbra/libs/org.apache.bcel_5.1.0/bcel.jar to YOURLOCATION

2. Checkout->Check out as a project configured using the new project wizard->finish
3. Java project->Next->Project name:bico->Finish

There will be errors in project to deal with them we must provide bcle.jar
4.bico->properieties->java build path->
a) add jars -> umbra->libs->org.apache.bcel_5.1.0
b) add external jars->YOURLOCATION
->bcel.jar->ok->ok