
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

public class ContractClause extends AstNode {



  public final List<Expression> preconditions;
  public final List<Expression> postconditions;


  // === Constructors and Factories ===
  protected ContractClause(List<Expression> preconditions, List<Expression> postconditions, SourceLocation location) {
    super(location);
    this.preconditions = preconditions; 
    this.postconditions = postconditions; 
  }

  public static ContractClause mk(List<Expression> preconditions, List<Expression> postconditions, SourceLocation location) {
    return new ContractClause(preconditions, postconditions, location);
  }

  // === Accessors ===

  public List<Expression> getPreconditions() { return preconditions; }
  public List<Expression> getPostconditions() { return postconditions; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitContractClause(this, preconditions, postconditions, getLocation());
  }

  // === Others ===
  @Override
  public ContractClause clone() {
    List<Expression> newPreconditions = preconditions;
    List<Expression> newPostconditions = postconditions;
    return ContractClause.mk(newPreconditions, newPostconditions, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

