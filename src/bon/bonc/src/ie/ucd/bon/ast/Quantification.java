
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class Quantification extends Expression {
  public static enum Quant {
    FORALL, 
    EXISTS
  }

  private final Expression restriction;
  private final Expression proposition;

  private final Quant quantifier;
  private final List<VariableRange> variableRanges;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected Quantification(Quant quantifier, List<VariableRange> variableRanges, Expression restriction, Expression proposition) {
    this(quantifier,variableRanges,restriction,proposition, null);    
  }

  protected Quantification(Quant quantifier, List<VariableRange> variableRanges, Expression restriction, Expression proposition, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.quantifier = quantifier; 
    this.variableRanges = variableRanges; 
    this.restriction = restriction; 
    this.proposition = proposition; assert proposition != null;
    
  }
  
  public static Quantification mk(Quant quantifier, List<VariableRange> variableRanges, Expression restriction, Expression proposition) {
    return new Quantification(quantifier, variableRanges, restriction, proposition);
  }

  public static Quantification mk(Quant quantifier, List<VariableRange> variableRanges, Expression restriction, Expression proposition, SourceLocation location) {
    return new Quantification(quantifier, variableRanges, restriction, proposition, location);
  }

  // === Accessors ===

  public Quant getQuantifier() { return quantifier; }
  public List<VariableRange> getVariableRanges() { return variableRanges; }
  public Expression getRestriction() { return restriction; }
  public Expression getProposition() { return proposition; }

  // === Others ===
  @Override
  public Quantification clone() {
    Quant newQuantifier = quantifier;
    List<VariableRange> newVariableRanges = variableRanges;
    Expression newRestriction = restriction == null ? null : restriction.clone();
    Expression newProposition = proposition == null ? null : proposition.clone();
    
    return Quantification.mk(newQuantifier, newVariableRanges, newRestriction, newProposition, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Quantification ast node: ");
    
    sb.append("quantifier = ");
    sb.append(quantifier);
    sb.append(", ");
    
    sb.append("variableRanges = ");
    sb.append(variableRanges);
    sb.append(", ");
    
    sb.append("restriction = ");
    sb.append(restriction);
    sb.append(", ");
    
    sb.append("proposition = ");
    sb.append(proposition);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

