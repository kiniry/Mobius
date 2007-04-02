This is the generic interface for a visitor that can return
a value. As a convenience, the object is also deconstructed
in the class. The original object is sent nevertheless because
we may want to use it.

\file{Evaluator.java}
/** 
  Public domain. 
  This file is generated from evaluator.tpl. Do not edit.
*/
package freeboogie.ast;

public abstract class Evaluator<R> {
\normal_classes{
  public abstract R eval(\ClassName \className, 
    \members[,]{
      \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType}
      \memberName
    }
  );
}
}
