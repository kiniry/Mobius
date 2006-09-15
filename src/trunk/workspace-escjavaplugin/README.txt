1. How to install the plugin in your Eclipse 3.2 development environment?
 a) Repeat the points b-f to the project modules: Simplify, Esctools,
    Escjava2UI, Escjava2Feature, Escjava2UpdateSite
    (note that the sequence of adding of the the modules is important).
 b) Choose a new eclipse project from CVS.
 c) Define or pick the proper CVS repository location (sth. like
    :ext:smbd@sort.ucd.ie:/cvsroot/escjava-eclipse).
 d) Pick a project module (e.g. Simplify).
 e) Check out as a project in workspace probably using the default
    workspace location.
 f) Use the PDE Tools menu after the right click of the mouse on the
    project to change the project to a plugin project.
 g) Now, you can develop the plugin. In particular, you can build
    it by going to the Escjava2UpdateSite, choosing site.xml, then 
    choosing the EscJava2 feature and pressing the Build button.
