
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

public class Quantification extends Expression {
  public static enum Quantifier {
    FORALL, 
    EXISTS
  }

  public final Expression restriction;
  public final Expression proposition;

  public final Quantifier quantifier;
  public final List<VariableRange> variableRanges;


  // === Constructors and Factories ===
  protected Quantification(Quantifier quantifier, List<VariableRange> variableRanges, Expression restriction, Expression proposition, SourceLocation location) {
    super(location);
    this.quantifier = quantifier; 
    this.variableRanges = variableRanges; 
    this.restriction = restriction; 
    this.proposition = proposition; assert proposition != null;
  }

  public static Quantification mk(Quantifier quantifier, List<VariableRange> variableRanges, Expression restriction, Expression proposition, SourceLocation location) {
    return new Quantification(quantifier, variableRanges, restriction, proposition, location);
  }

  // === Accessors ===

  public Quantifier getQuantifier() { return quantifier; }
  public List<VariableRange> getVariableRanges() { return variableRanges; }
  public Expression getRestriction() { return restriction; }
  public Expression getProposition() { return proposition; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitQuantification(this, quantifier, variableRanges, restriction, proposition, getLocation());
  }

  // === Others ===
  @Override
  public Quantification clone() {
    Quantifier newQuantifier = quantifier;
    List<VariableRange> newVariableRanges = variableRanges;
    Expression newRestriction = restriction == null ? null : restriction.clone();
    Expression newProposition = proposition == null ? null : proposition.clone();
    return Quantification.mk(newQuantifier, newVariableRanges, newRestriction, newProposition, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

