This is the README file for the Beetlz application.
It describes the contents of this distribution and its use.

Author: Eva Darulova
Institution: University College Dublin
Contact: edarulova@googlemail.com
Date: 8th May 2009
Version: beta-1

================== Description ==================    
Beetlz is a consistency checker for BON and Java, developed as part of
an undergraduate final year project. 
It takes your source files as input and returns feedback on whether and
where they are inconsistent. The tool is available in a command-line and 
in a Eclipse plugin version.

==================  Contents  ===================
- source code
- all required libraries
- sample test code
- various documents: 
	- presentation and posters from UCD final year
	- plugin screenshots from Windows 
- notes for development (work in progress/planned)
 

============= Technical Requirements =============
Minimum Java requirement		Java 1.6
Supported platforms  			Platform independent
Supported platforms (plugin)	Mac OS X, Linux



================== Installation ==================
Creating a runnable Jar file, produces a command-line version that 
is ready for use as is. To run the tool from its installation directory:
java -jar beetlz.jar < options > 

To install the Eclipse plugin (Having deployed the BeetlzPlugin):
- place the BeetlzPlugin.jar into the 'plugins' directory in your Eclipse 
distribution. Restarting Eclipse will install Beetlz. If this should not be the case, 
run Eclipse with the option -clean once.  
- now navigate to the Beetlz Preference page (Window -> Preferences -> Beetlz) and 
select the openjml.jar file supplied with this distribution as the specs file. 
If you want to use your own specificiation files for OpenJML, select it instead.
- to check Beetlz is installed, select a project in the Package Explorer. 
Right-clicking on the project will reveal Beetz as an entry in the menu.



============ Configuration Command line ===========
Command-line version:
Beetlz: consistency checker for BON and Java/JML.
Usage: beetlz [<options>] -files <source files or directories>
Automatically recognized source file extensions are:
.bon, .java, specification files are automatically recognised and 
must NOT be explicitly added
options are: 
-help 				 Print this help 
-pureBON 			 Only use original, not extended, BON 
-source {bon, java} 		 Which files to use as source 
-userSettings file 		 Custom user settings  
-skeleton [dir] 		 Print skeleton code from source and place into directory 
-skeletonOneFile 		 Print skeleton code into 1 file.
-verbose 			 Generate debugging info  
-noJML 			 Do not check and ignore JML and assertion language  
-noJava 			 Do not print Java related errors and warnings 
-noError 			 Do not print errors  
-noWarning 			 Do not print warnings  
-noBasics 			 Do not use basic settings 
-noNullCheck 			 Do not check for correct nullity

JML options:
-specs-specs			 Specifies the directory path to search for specification files

*Error filtering
  By default, all errors will be shown, but each type (error or warning) 
  may be filtered out.
*No JML or no Java 
  The consistency check may be limited to Java only constructs and thus ignore all assertion 
  related elements. Note that using this switch will also ignore all defined model fields and 
  methods and ghost fields. Or otherwise one may limit the error messages to JML-related 
  ones only as well.
*Pure BON 
  In a few places, the tool extends the original BON definition and if desired the option 
  exists to use the unaltered BON definition.
  In particular: 
  constructors are ignored 
  enumerated type definitions are ignored and treated as normal classes
  history constraints are ignored 
*Source selection 
  For a consistency check, the source input is assumed to be the `correct' version of the 
  project so that errors are related to the target files. By default this selection is made 
  based on the latest time stamp of the files, so that most recently edited files are assumed 
  `correct'. In general, this selection will be appropriate, but it can be overridden if desired. 
*Nullity checks 
  As mentioned previously, BON and JML have different default assumptions when it comes to null 
  references. This can potentially cause a great amount of (unwanted) error messages. This option 
  will disregard these.
*Skeleton generation 
  If the skeleton code option is selected, no consistency check will be performed, instead the 
  source input will be printed in its corresponding representation in the target language. 
  In this case the source option may be useful to force the tool to print in the correct 
  programming language. Optionally, a directory can be supplied, so that the result will not be 
  printed to standard output but to one or more files. 
*User Settings file
  Beetlz currently includes mappings for BON basic types to the most common types in Java. 
  In many cases, the user will want to extend this list by custom types and can do so by supplying 
  Beetlz with a text file with these mappings. Additionally, mappings for class and feature/method 
  names can be specified as well, enabling the user to give hints to the tool to make the 
  consistency check as accurate as possible. 
*JML specs 
  By default, OpenJML internal specification files are used to parse and check Java input files. 
  If the user wishes to use their own, potentially more complete ones, he can do so using this option.

============== Configuration Eclipse plugin ===============
These options can also be selected on the Preference page and some on the GUI popups, 
which will appear when the Beetlz option is selected from the menu. Custom setting files and 
skeleton directories can only be selected on the Preference page. Note: those settings are 
workspace-wide, so when you change projects you are checking, don't forget to change 
the custom settings file as well. 


=========== Format of the custom settings file ============
-- Comments are introduced by double dashes;
-- every line has to end with a semicolon;

-- Mappings for feature names, Java names must be fully qualified; 
feature_mapping pattern@SNAKE getPattern@zoo.animal.Snake;
feature_mapping asleep@ZEBRA sleeping@zoo.animal.Zebra;

-- Mappings for class names;
class_mapping LION zoo.animal.AbstractLion;

-- Ignore prefixes on field names, separated by empty space;
ignore_prefix my_ _;

-- Ignored classes, BON names first;
-- If no BON or Java names are ignored, include empty brackets; 
ignore_classes {} {zoo.personnels.Snake};
ignore_classes {KEEPER, MANAGER} {zoo.personnel.Keeper$Mop};



======================== Known bugs =======================
- default package
Classes in default packages will result in errors. To prevent these, place those classes 
in a package called 'defaultpackage'. This name is recognised by Beetlz as default package.




======================== Test code ========================
The distribution includes two sets of test files, located in the tests directory. 
zoo and zoo_faulty contain the same classes, in Java and in BON, where the files in zoo will 
have a 'clean' consistency run (no faults), and the files in zoo_faulty will generate 
several errors.
The easiest way, provided you have the project open in Eclipse, is to run
tests/RunACheck.java, tests/RunAPrettyprintTest.java, tests/RunATest.java.




======================= Troubleshooting ====================
1) The plugin does not appear.
Eclipse will not issue a warning, even if there are problems. If the plugin does not appear, 
check that Eclipse is indeed running the required Java version. It may not necessarily use the 
latest version, so make sure that uses Java 1.6.

2) When running the consistency checker, I get compile errors, even though the source has 
compiled fine. 
This may be the case, if you have additional .java or .bon files in the directory you specified. 
Beetlz searches recursively and will take any file with extension .java and .bon. If you have 
files not intended for check, then do not add the whole directory but individual files. This 
problem may also occur, when skeleton code is produced and subsequently included in consistency 
checks, producing duplicate declarations.

3) I get compile errors, but the consistency checker still produces output.
If there are no major compile errors in the Java code, the source will still be processed, 
ignoring the faults. If you don't care much about the errors presented, ignore them. 
BON compile errors will always result in aborting the tool.
The list of errors, particularly in Eclipse may appear as a major error, since it will appear as
a popup. However, if the potential errors were only listed in the console, they would disapper 
behind all other output.

