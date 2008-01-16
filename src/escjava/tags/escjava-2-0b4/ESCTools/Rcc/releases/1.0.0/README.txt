RCC 1.0.0 - a race condition checker for Java

Welcome
  Annotated Java 1.4 programs that pass RCC tests are guaranteed
  to be free of data races. You also need a Java 1.4 to run the
  tool itself. Before continuing to read me please take a look
  at the examples directory.

Reference of RCC annotations
  Type VarName /*#guarded_by*/ LockSet
    Whenever VarName is accessed all locks in LockSet should be held.

  ReturnType MethodName(Args) /*#requires LockSet*/ {Body}
    Whenever MethodName is called all locks in LockSet should be held.

  ClassName /*#{ghost Object LockSet}*/ {ClassBody}
  ClassName/*#{LockSet}*/ VarName
    The first annotation gives a list of formal locks. (Ignore
    "ghost Object".) The second annotation provides the actual
    `external' locks to be used.

  /*#thread_local*/ ClassDeclaration
  /*#thread_shared*/ ClassDeclaration
    All objects of a class are considered to be either local or shared.
    If an object is shared then all its fields are also shared.
    A shared field must be either final, volatile, or guarded by
    a lock. Its class must be thread shared.

  Escape mechanisms reduce the number of unwanted warnings. See
  the article cited below for details. 


Authors
  This tool was developed as a prototype by Cormac Flanagan and 
  Stephen Freund. A thorough description of the theoretical 
  underpinnings can be found in [Types for Safe Locking: Static 
  Race Detection for Java, M. Abadi, C. Flanagan, S. Freund, 
  TOPLAS 2006]. The tool was revived in 2007 by Radu Grigore.
  All bugs are his.


