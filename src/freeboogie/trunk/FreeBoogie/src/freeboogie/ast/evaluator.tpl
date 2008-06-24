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
package freeboogie.ast;
import java.math.BigInteger;
import java.util.HashMap;

/**
  Use as a base class when you want to compute a value of type
  {@code R} for each node. An example is the typechecker.
 */
public class Evaluator<R> {
  private HashMap<Ast, R> cache = new HashMap<Ast, R>();

  public R get(Ast a) { return cache.get(a); }
  protected R memo(Ast a, R r) { 
    if (r != null) cache.put(a, r);
    return r;
  }

\normal_classes{
  public R eval(\ClassName \className, 
    \members[,]{
      \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType}
      \memberName
    }
  ) {
    enterNode(\className);
    \children{if (\memberName != null) \memberName.eval(this);}
    exitNode(\className);
    return null;
  }
}
  // allows the user to visit nodes and distingush them by some
  // other criterion than type
  public void enterNode(Ast ast) {}
  public void exitNode(Ast ast) {}
}

\file{AssociativeEvaluator.java}
/**
  This file is generated from evaluator.tpl. Do not edit.
 */
package freeboogie.ast;
import java.math.BigInteger;

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
    R result_ = assocOp.zero();
    enterNode(\className);
    \children{if (\memberName != null) 
      result_ = assocOp.plus(result_, \memberName.eval(this));}
    exitNode(\className);
    return memo(\className, result_);
  }
}
}
