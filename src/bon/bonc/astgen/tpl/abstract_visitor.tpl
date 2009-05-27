This is the generic interface for a visitor.

\file{AbstractVisitor.java}
/** 
  This file is generated from abstract_visitor.tpl. Do not edit.
 */
package \Userdefine{pkg};

import java.util.List;

public abstract class AbstractVisitor implements IVisitor {


\normal_classes{
  public void visit\ClassName(\ClassName node,\members[,]{ \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType} \memberName}) {
    //Do nothing
  }
}
}

\file{IVisitor.java}
/** 
  This file is generated from abstract_visitor.tpl. Do not edit.
 */
package \Userdefine{pkg};

import java.util.List;

public interface IVisitor {


\normal_classes{
  void visit\ClassName(\ClassName node,\members[,]{ \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType} \memberName });
}
}