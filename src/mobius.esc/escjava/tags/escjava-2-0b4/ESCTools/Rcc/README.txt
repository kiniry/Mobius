RCC - a race condition checker for Java

Dependencies
  The library `javafe-1.0.jar' should be placed in the `lib' directory.
  This file is obtained by running `make jar' in Javafe.
  We use `ant' as the build tool; it should be installed.
  
Compilation
  Run `ant' in the same directory as this README file.

Usage
  Add the directory that contains this README file to your PATH.
  Then use the command `rcc'.
  
Authors
  Cormac Flanagan and Stephen Freund
  Since 2006, Radu Grigore has started to introduce bugs.
  
RCC annotations
  Before reading on you should look at the test/functional directory
  to see some examples. Here we give a comprehensive but rather arcane
  list of all annotations understood by RCC. In general RCC is rather
  forgiving about the placement of annotations. All the new syntax should
  be enclosed by /*# stylized comments */. The style will be changed
  soon to the /*@ JML style */.

  Meta symbols:
    ls---lock set
    fls---formal lock set
    fd---field declaration
    cd---class declaration
    cn---class name
    cb---class body
    fn---field name
    md---method declaration
  The annotations
    fd guarded_by ls;  --- fd
    requires ls md;    --- md

    cn {ghost fls} cb  --- cd
    cn {ls} fn;        --- fd

    thread_local cd;   --- cd
    thread_shared cd;  --- cd

