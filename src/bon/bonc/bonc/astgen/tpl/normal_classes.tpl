This template generates java classes for the normal classes.

\normal_classes{\file{\ClassName.java}
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package \Userdefine{pkg};

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class \ClassName extends \Basename {
\enums{  public static enum \EnumName {\values[, ]{
    \VALUE_NAME}
  }}
\invariants{  //@ invariant \inv_text;
}
\children{  public final \MemberType \memberName;
}
\primitives{  public final \Membertype \memberName;
}

  // === Constructors and Factories ===
  protected \ClassName(\members[, ]{\if_primitive{\Membertype}{\MemberType} \memberName}, SourceLocation location) {
    super(location);
\members{    this.\memberName = \memberName; \if_nonnull{assert \memberName != null;}{}
}  }
  
  public static \ClassName mk(\members[, ]{\if_primitive{\Membertype}{\MemberType} \memberName}, SourceLocation location) {
    return new \ClassName(\members[, ]{\memberName}, location);
  }

  // === Accessors ===
\members{
  public \if_primitive{\Membertype}{\MemberType} get\MemberName() { return \memberName; }}

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visit\ClassName(this,\members[,]{ \memberName}, getLocation());
  }

  // === Others ===
  @Override
  public \ClassName clone() {
    \members{\if_primitive{\Membertype new\MemberName = \memberName;}{\MemberType new\MemberName = \memberName == null ? null : \memberName.clone();}
    }return \ClassName.mk(\members[, ]{new\MemberName}, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("\ClassName ast node: ");
\members{    sb.append("\memberName = ");
    sb.append(\memberName);
    sb.append(", ");
    }if (sb.length() >= 2) {
      sb.delete(sb.length()-2, sb.length());
    }
    return sb.toString();
  }
}

