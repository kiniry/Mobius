
\file{Substitutor.java}
/* Generated from substitutor.tpl. Do not edit */
package \Userdefine{pkg};

import java.util.Map;

/**
  Substitutes pieces of an AST with other AST pieces.

 */
public class Substitutor extends Transformer {
  private Map<\Userdefine{defaultBaseName}, \Userdefine{defaultBaseName}> subst;

  public Substitutor(Map<\Userdefine{defaultBaseName}, \Userdefine{defaultBaseName}> subst) {
    this.subst = subst;
  }

  \normal_classes{
    @Override public \Userdefine{defaultBaseName} eval(
      \ClassName \className,
      \members[, ]{\if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType}
        \memberName}
    ) {
      \Userdefine{defaultBaseName} r = subst.get(\className);
      return r == null ? \className : r;
    }
  }
}
