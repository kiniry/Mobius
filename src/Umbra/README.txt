HOWTO INSTALL UMBRA

1) Copy org.apache.bcel_5.1.0 from libs and paste it into your_eclipse_directory/plugins/
2) R-click Umbra and choose checkout
3) Select -> check out as a project configured using the New Project Wizard
4) Choose Plug-in Project and type:
5) name: umbra
6) source folder name: source
7) next -> finish

SOME ECLIPSE PROBLEMS:
* FileEditorInput malaise...
- access rules for org.eclips.ui.ide are WRONG!!!! (e.g. in eclipse 3.2.2 coming from Ubuntu 7.04)
- they can be changed in umbra project properties (select "Properties" from the mouse context menu ;)
  Then: Java Build Path - Libraries - Plug-in Dependencies - (unfold) - Access rules - Edit - Ugh
- they are stored in the .classpath file