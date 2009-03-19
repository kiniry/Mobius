This is the generic interface for a visitor that can return
a value. As a convenience, the object is also deconstructed
in the class. The original object is sent nevertheless because
we may want to use it.

TODO: Consider having a base class for this which is parametrized
by the return type for each type of node.

\file{Evaluator.java}
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
public class Evaluator<R> {
  protected HashMap<Ast, R> evalCache = new HashMap<Ast, R>();
  protected R memo(Ast a, R r) { 
    if (r != null) evalCache.put(a, r);
    return r;
  }
  public R get(Ast a) { return evalCache.get(a); }

\normal_classes{
  public R eval(\ClassName \className, 
    \members[,]{
      \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType}
      \memberName
    }
  ) {
    if (evalCache.containsKey(\className)) return evalCache.get(\className);
    enterNode(\className);
    \children{if (\memberName != null) \memberName.eval(this);}
    exitNode(\className);
    return null;
  }
}
  public void enterNode(Ast ast) {}
  public void exitNode(Ast ast) {}
}

\file{AssociativeEvaluator.java}
/**
  This file is generated from evaluator.tpl. Do not edit.
 */
package \Userdefine{pkg};
import java.util.*;
import mobius.logic.lang.ast.AssociativeOperator;

public class AssociativeEvaluator<R> extends Evaluator<R> {
  protected AssociativeOperator<R> assocOp;
  public AssociativeEvaluator(AssociativeOperator<R> assocOp) {
    this.assocOp = assocOp;
  }
\normal_classes{
  @Override public R eval(\ClassName \className,
    \members[,]{
      \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType}
      \memberName
    }
  ) {
    if (evalCache.containsKey(\className)) return evalCache.get(\className);
    R result_ = assocOp.zero();
    enterNode(\className);
    \children{if (\memberName != null) 
      result_ = assocOp.plus(result_, \memberName.eval(this));}
    exitNode(\className);
    return memo(\className, result_);
  }
}
}
