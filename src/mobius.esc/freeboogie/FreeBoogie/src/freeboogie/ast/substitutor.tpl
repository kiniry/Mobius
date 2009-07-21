
\file{Substitutor.java}
/* Generated from substitutor.tpl. Do not edit */
package freeboogie.ast;

import java.util.Map;
import java.math.BigInteger;

/**
  Substitutes pieces of an AST with other AST pieces.

 */
public class Substitutor extends Transformer {
  private Map<Ast, Ast> subst;

  public Substitutor(Map<Ast, Ast> subst) {
    this.subst = subst;
  }

  \normal_classes{
    @Override public Ast eval(
      \ClassName \className,
      \members[, ]{\if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType}
        \memberName}
    ) {
      Ast r = subst.get(\className);
      return r == null ? \className : r;
    }
  }
}
