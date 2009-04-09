
Apache ANT Merge and Diff Tasks

. Setup

  setup the classpath ref for the Task

  For example:

   <path id="merge.path">
     <fileset dir="${lib.dir}" >
       <include  name="**/*.jar"/>
     </fileset>
     <pathelement path="${classpath}"/>
   </path>


   define the taskdef for Merge or Diff or Both in your
   ant xml file.

   <!-- merge task -->
   <taskdef classname="org.apache.tools.ant.taskdefs.Merge"
            classpathref="merge.path"
            name="merge"/>         

   <!-- diff task -->
   <taskdef classname="org.apache.tools.ant.taskdefs.Diff"
            classpathref="diff.path"
            name="diff"/>   


  Basic usage is that one is either diff'ing from one file to
  another (the diff of the "from" file from the "to" file). The
  code always assumes the "to" is the file that one is the primary
  file.


. Merge

  Merge either merges different source trees or 2 different
  files.

  Merge shares attributes with those used by the Ant Task Patch

  ["ignorewhitespace" is optional. if it's not defined then it defaults to false.]
  ["strip" is optional. if it's not defined then it is not used.]
  ["quiet" is optional. if it's not defined then it defaults to false.]
  ["reverse" is optional. if it's not defined then it will not revere patch the diff.]
  ["backups" is optional. if it's not defined then it will default to false and no
                          backup file (pre-merge) will be created]


  To merge 2 different files the attributes "tofile" and
  "fromfile" are used 

  ["diffdir" is optional. if it's not defined then the diff output files will be
                          placed in the basedir]

  ["forcediff" is optional. if it's not defined then it defaults to false.]

  ["difftype" is optional. if it's not defined then the diff output files will be
                          in the Context format. Supported values are:
                          -n   Normal Formatting
                          -c   Context Formatting
                          -u   Unified Formatting
                          -e   Ed      Formatting
  ]

  Example

   <merge tofile="test/foo/D.1"
          fromfile="test/bar/D.1"
          diffdir="test/diff"
          forcediff="true"
          ignorewhitespace="false" />

  To merge 2 seperate source trees the attributes "todir" and
  "diffdif" are used.

  ["fromdir" can be used to define the from directory or a fileset]
   
  Example

   <merge todir="test/foo"
          diffdir="test/diff"
          difftype="-u"
          forcediff="true"
          ignorewhitespace="false" >
    <fileset dir="test/bar">
     <include  name="**/*"/>
    </fileset>
   </merge>



. Diff

  Diff only diffs 2 different files.

  To diff 2 different files the attributes "tofile" and
  "fromfile" are defined.

  ["difffile" is optional. It defines where to put the diff output, if it's undefined
                           then it will be placed in the basedir.]

  ["difftype" is optional. if it's not defined then the diff output files will be
                          in the Context format. Supported values are:
                          -n   Normal Formatting
                          -c   Context Formatting
                          -u   Unified Formatting
                          -e   Ed      Formatting
  ]

  Example

   <diff tofile="mymaintree/src/foo/MyClass.java"
         fromfile="mybranch/src/foo/MyClass.java"
         difffile="mymaintree/src/foo/MyClass.java.diff" />


   <diff tofile="mymaintree/src/bar/MyOtherClass.java"
         fromfile="mybranch/src/bar/MyOtherClass.java"
         difftype="-e"
         difffile="mymaintree/src/bar/MyOtherClass.java.diff" />



Enjoy

Any bugs or issues please send to b.kyer _at_ hydrogenline.com (NOSPAM PLEASE)


. Misc

  The diff generation is done using the source files retrieved from

  http://bmsi.com/java/#diff

  They are slightly modified to support doing the DiffPrint in a doWork method
  instead of a static main method (as well as support for passing a Writer
  to the DiffPrint from another class easily.

  Updated license to be completely GPL to meet GPL criteria since GPL'd code
  was used as the underlying functionality

. Known Issues

- Patch behaves erratically on Windows XP (cygwin/mks) when doing the patch update
  causing unexpected rejections or "access denied" when writing the updated file.


. Latest Code is available from http://www.hydrogenline.com/ant/ant_md.zip

