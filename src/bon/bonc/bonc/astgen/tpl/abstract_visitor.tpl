This is the generic interface for a visitor.

\file{AbstractVisitor.java}
/** 
  This file is generated from abstract_visitor.tpl. Do not edit.
 */
package \Userdefine{pkg};

import java.util.Collection;
import java.util.List;

import ie.ucd.bon.source.SourceLocation;

public abstract class AbstractVisitor implements IVisitor {

\normal_classes{
  public void visit\ClassName(\ClassName node,\members[,]{ \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType} \memberName}, SourceLocation loc) {
    //Do nothing
  }
  
}

  public void visitAll(Collection<? extends AstNode> nodes) {
    if (nodes != null) {
      for (AstNode node : nodes) {
        node.accept(this);
      }
    }
  }
  
  public void visitNode(AstNode node) {
    if (node != null) {
      node.accept(this);
    }
  }

}

\file{IVisitor.java}
/** 
  This file is generated from abstract_visitor.tpl. Do not edit.
 */
package \Userdefine{pkg};

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public interface IVisitor {


\normal_classes{
  void visit\ClassName(\ClassName node,\members[,]{ \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType} \memberName }, SourceLocation loc);
}
}