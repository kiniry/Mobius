SOME ECLIPSE PROBLEMS:
* FileEditorInput malaise...
- access rules for org.eclips.ui.ide are WRONG!!!! (e.g. in eclipse 3.2.2 coming from Ubuntu 7.04)
- they can be changed in umbra project properties (select "Properties" from the mouse context menu ;)
  Then: Java Build Path - Libraries - Plug-in Dependencies - (unfold) - Access rules - Edit - Ugh
- they are stored in the .classpath file


BytecodeTagScanner
TagRule