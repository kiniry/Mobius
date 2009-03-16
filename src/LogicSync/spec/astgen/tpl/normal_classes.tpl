This template generates java classes for the normal classes.

\normal_classes{\file{\ClassName.java}
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package \Userdefine{pkg};
import java.math.BigInteger; // for AtomNum

import mobius.logic.lang.ast.FileLocation;
import mobius.logic.lang.ast.IEvaluator;

/** @author rgrig */
public final class \ClassName extends \Basename {
\enums{  public static enum \EnumName {\values[, ]{
    \VALUE_NAME}
  }}
\invariants{  //@ invariant \inv_text;
}
\children{  private final \MemberType \memberName;
}
\primitives{  private final \Membertype \memberName;
}

  // === Constructors and Factories ===
  private \ClassName(\members[, ]{\if_primitive{\Membertype}{\MemberType} \memberName}) {
    this.location = FileLocation.unknown();
\members{    this.\memberName = \memberName; \if_nonnull{assert \memberName != null;}{}
}  }

  private \ClassName(\members[, ]{\if_primitive{\Membertype}{\MemberType} \memberName}, FileLocation location) {
    this(\members[,]{\memberName});
    assert location != null;
    this.location = location;
  }
  
  public static \ClassName mk(\members[, ]{\if_primitive{\Membertype}{\MemberType} \memberName}) {
    return new \ClassName(\members[, ]{\memberName});
  }

  public static \ClassName mk(\members[, ]{\if_primitive{\Membertype}{\MemberType} \memberName}, FileLocation location) {
    return new \ClassName(\members[, ]{\memberName}, location);
  }

  // === Accessors ===
\members{
  public \if_primitive{\Membertype}{\MemberType} get\MemberName() { return \memberName; }}

  // === The Visitor pattern ===
  @Override
  public <R> R eval(IEvaluator<R> evaluator) { 
    return evaluator.eval(this, \members[,]{\memberName}); 
  }

  // === Others ===
  @Override
  public \ClassName clone() {
    \members{
      \if_primitive{
        \Membertype new\MemberName = \memberName;
      }{
        \MemberType new\MemberName = \memberName == null? 
          null : \memberName.clone();
      }
    }
    return \ClassName.mk(\members[, ]{new\MemberName}, location);
  }
}

