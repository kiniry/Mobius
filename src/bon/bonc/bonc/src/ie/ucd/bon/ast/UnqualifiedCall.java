
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class UnqualifiedCall extends AstNode {



  public final String id;
  public final List<Expression> args;


  // === Constructors and Factories ===
  protected UnqualifiedCall(String id, List<Expression> args, SourceLocation location) {
    super(location);
    this.id = id; assert id != null;
    this.args = args; assert args != null;
    
  }
  
  public static UnqualifiedCall mk(String id, List<Expression> args, SourceLocation location) {
    return new UnqualifiedCall(id, args, location);
  }

  // === Accessors ===

  public String getId() { return id; }
  public List<Expression> getArgs() { return args; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitUnqualifiedCall(this, id, args, getLocation());
  }

  // === Others ===
  @Override
  public UnqualifiedCall clone() {
    String newId = id;
    List<Expression> newArgs = args;
    
    return UnqualifiedCall.mk(newId, newArgs, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("UnqualifiedCall ast node: ");
    
    sb.append("id = ");
    sb.append(id);
    sb.append(", ");
    
    sb.append("args = ");
    sb.append(args);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

