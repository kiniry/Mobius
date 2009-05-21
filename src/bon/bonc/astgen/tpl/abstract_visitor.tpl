This is the generic interface for a visitor.

\file{AbstractVisitor.java}
/** 
  This file is generated from evaluator.tpl. Do not edit.
 */
package \Userdefine{pkg};

public abstract class AbstractVisitor implements IVisitor {


\normal_classes{
  public void visit\ClassName(\ClassName node) {
    //Do nothing
  }
}
}

\file{IVisitor.java}
/** 
  This file is generated from evaluator.tpl. Do not edit.
 */
package \Userdefine{pkg};

public interface IVisitor {


\normal_classes{
  void visit\ClassName(\ClassName node);
}
}