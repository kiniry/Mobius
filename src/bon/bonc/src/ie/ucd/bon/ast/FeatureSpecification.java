
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class FeatureSpecification extends AstNode {
  public static enum Modifier {
    NONE, 
    DEFERRED, 
    REDEFINED, 
    EFFECTIVE
  }

  private final ContractClause contracts;
  private final HasType hasType;
  private final RenameClause renaming;

  private final Modifier modifier;
  private final List<String> featureNames;
  private final List<FeatureArgument> arguments;
  private final String comment;


  // === Constructors and Factories ===
  protected FeatureSpecification(Modifier modifier, List<String> featureNames, List<FeatureArgument> arguments, ContractClause contracts, HasType hasType, RenameClause renaming, String comment, SourceLocation location) {
    super(location);
    this.modifier = modifier; 
    this.featureNames = featureNames; assert featureNames != null;
    this.arguments = arguments; assert arguments != null;
    this.contracts = contracts; assert contracts != null;
    this.hasType = hasType; 
    this.renaming = renaming; 
    this.comment = comment; 
    
  }
  
  public static FeatureSpecification mk(Modifier modifier, List<String> featureNames, List<FeatureArgument> arguments, ContractClause contracts, HasType hasType, RenameClause renaming, String comment, SourceLocation location) {
    return new FeatureSpecification(modifier, featureNames, arguments, contracts, hasType, renaming, comment, location);
  }

  // === Accessors ===

  public Modifier getModifier() { return modifier; }
  public List<String> getFeatureNames() { return featureNames; }
  public List<FeatureArgument> getArguments() { return arguments; }
  public ContractClause getContracts() { return contracts; }
  public HasType getHasType() { return hasType; }
  public RenameClause getRenaming() { return renaming; }
  public String getComment() { return comment; }

  // === Visitor ===
  public void accept(IVisitor visitor) {
    visitor.visitFeatureSpecification(this, modifier, featureNames, arguments, contracts, hasType, renaming, comment);
  }

  // === Others ===
  @Override
  public FeatureSpecification clone() {
    Modifier newModifier = modifier;
    List<String> newFeatureNames = featureNames;
    List<FeatureArgument> newArguments = arguments;
    ContractClause newContracts = contracts == null ? null : contracts.clone();
    HasType newHasType = hasType == null ? null : hasType.clone();
    RenameClause newRenaming = renaming == null ? null : renaming.clone();
    String newComment = comment;
    
    return FeatureSpecification.mk(newModifier, newFeatureNames, newArguments, newContracts, newHasType, newRenaming, newComment, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("FeatureSpecification ast node: ");
    
    sb.append("modifier = ");
    sb.append(modifier);
    sb.append(", ");
    
    sb.append("featureNames = ");
    sb.append(featureNames);
    sb.append(", ");
    
    sb.append("arguments = ");
    sb.append(arguments);
    sb.append(", ");
    
    sb.append("contracts = ");
    sb.append(contracts);
    sb.append(", ");
    
    sb.append("hasType = ");
    sb.append(hasType);
    sb.append(", ");
    
    sb.append("renaming = ");
    sb.append(renaming);
    sb.append(", ");
    
    sb.append("comment = ");
    sb.append(comment);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

