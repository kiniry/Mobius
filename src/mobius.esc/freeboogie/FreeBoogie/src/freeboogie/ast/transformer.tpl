vim:filetype=java:

\file{Transformer.java}
/**
  This file was generated from transformer.tpl. Do not edit.
 */
package freeboogie.ast;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.Deque;

import freeboogie.tc.TcInterface;
import freeboogie.tc.TypeUtils;

/**
  Intended to be used as a base class by visitors that either
  only inspect the AST or transform the AST. If you want to
  inspect nodes of type X into then you should override {@code
  see(X x, ...)}. (Most of the time you also need to code
  visiting of the children.) If you want to replace (some) nodes
  of type X by something you should override {@code eval(X x,
  ...)} and return the substitution. This class will take care of
  path copying.
  
  @see freeboogie.ast.Evaluator
 */
public class Transformer extends Evaluator<Ast> {
  private final Ast NULL = AtomId.mk("<NULL>",null);
  private Deque<Ast> result = new ArrayDeque<Ast>();
  protected TcInterface tc;

  /** Returns the name of this transformer. */
  public String name() {
    return getClass().getName();
  }

  public Program process(Program p, TcInterface tc) {
    return new Program(process(p.ast, tc), p.fileName);
  }

  public Declaration process(Declaration ast, TcInterface tc) {
    this.tc = tc;
    return TypeUtils.internalTypecheck((Declaration)ast.eval(this), tc);
  }

\normal_classes{

  public void see(
    \ClassName \className,
    \members[,]{
      \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType} 
      \memberName
    }
  ) {
    assert \className != null;
    boolean sameChildren = true;
    \members{
      \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType}
      new\MemberName = 
        \if_primitive{\memberName}{
          \memberName == null ? null :(\MemberType)\memberName.eval(this)
        };
      \if_primitive{}{sameChildren &= new\MemberName == \memberName;}
    }

    if (!sameChildren) {
      result.removeFirst();
      result.addFirst(\ClassName.mk(\members[,]{new\MemberName},\className.loc()));
    }
  }
  
  @Override
  public Ast eval(
    \ClassName \className,
    \members[,]{
      \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType} 
      \memberName
    }
  ) {
    // Deque<> doesn't support null elements
    result.addFirst(\className == null ? NULL : \className);
    enterNode(\className);
    see(\className,\members[,]{\memberName});
    exitNode(\className);
    Ast r = result.removeFirst();
    return r == NULL ? null : r;
  }
}
}

\file{visitor.skeleton}
// You can copy and paste the text below when you define a visitor that
// needs to override most functions on the base class.

\normal_classes{  @Override
  public void see(\ClassName \className, \members[, ]{\if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType} \memberName}) {
    assert false : "not implemented";
  }
  
}

// *********

\normal_classes{  @Override
  public \ClassName eval(\ClassName \className, \members[, ]{\if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType} \memberName}) {
    assert false : "not implemented";
    return null;
  }

}

