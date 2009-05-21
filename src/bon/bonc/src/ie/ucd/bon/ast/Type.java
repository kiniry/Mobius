
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class Type extends AstNode {



  private final String identifier;
  private final List<BONType> actualGenerics;
  private final String fullString;


  // === Constructors and Factories ===
  protected Type(String identifier, List<BONType> actualGenerics, String fullString, SourceLocation location) {
    super(location);
    this.identifier = identifier; assert identifier != null;
    this.actualGenerics = actualGenerics; assert actualGenerics != null;
    this.fullString = fullString; assert fullString != null;
    
  }
  
  public static Type mk(String identifier, List<BONType> actualGenerics, String fullString, SourceLocation location) {
    return new Type(identifier, actualGenerics, fullString, location);
  }

  // === Accessors ===

  public String getIdentifier() { return identifier; }
  public List<BONType> getActualGenerics() { return actualGenerics; }
  public String getFullString() { return fullString; }

  // === Visitor ===
  public void accept(IVisitor visitor) {
    visitor.visitType(this);
  }

  // === Others ===
  @Override
  public Type clone() {
    String newIdentifier = identifier;
    List<BONType> newActualGenerics = actualGenerics;
    String newFullString = fullString;
    
    return Type.mk(newIdentifier, newActualGenerics, newFullString, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Type ast node: ");
    
    sb.append("identifier = ");
    sb.append(identifier);
    sb.append(", ");
    
    sb.append("actualGenerics = ");
    sb.append(actualGenerics);
    sb.append(", ");
    
    sb.append("fullString = ");
    sb.append(fullString);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

