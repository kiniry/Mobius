This is the generic interface for a visitor that can return
a value. As a convenience, the object is also deconstructed
in the class. The original object is sent nevertheless because
we may want to use it.

TODO: Consider having a base class for this which is parametrized
by the return type for each type of node.

\file{AEvaluator.java}
/** 
  This file is generated from evaluator.tpl. Do not edit.
 */
package \Userdefine{pkg};
import java.math.BigInteger;
import java.util.*;

import mobius.logic.lang.ast.Ast;

/**
  Use as a base class when you want to compute a value of type
  {@code R} for each node. An example is the typechecker.
 */
public abstract class AEvaluator<R> extends Evaluator<R>{


\normal_classes{
  public abstract R eval\ClassName(
    \members[,]{
      \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType}
      \memberName
    }
  );
  public R eval(\ClassName \className, 
    \members[,]{
      \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType}
      \memberName
    }
  ) {
    if (evalCache.containsKey(\className)) return evalCache.get(\className);
    R localResult = null;
    enterNode(\className);
    localResult = eval\ClassName(\members[,]{\memberName});
    exitNode(\className);
    return localResult;
  }
}
}
