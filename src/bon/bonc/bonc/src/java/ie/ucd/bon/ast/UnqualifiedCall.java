
/**
 * Copyright (c) 2007-2010, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 *
 * This class is generated automatically from normal_classes.tpl.
 * Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.util.StringUtil;

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
    return StringUtil.prettyPrint(this);
  }
}

