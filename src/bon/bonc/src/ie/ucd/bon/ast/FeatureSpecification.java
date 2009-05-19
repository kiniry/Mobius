
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class FeatureSpecification extends AstNode {


  private final HasType hasType;
  private final RenameClause renaming;
  private final ContractClause contracts;

  private final List<String> featureNames;
  private final Boolean deferred;
  private final Boolean effective;
  private final Boolean redefined;
  private final List<FeatureArgument> arguments;
  private final String comment;

private final SourceLocation location;

  // === Constructors and Factories ===
  protected FeatureSpecification(List<String> featureNames, Boolean deferred, Boolean effective, Boolean redefined, List<FeatureArgument> arguments, HasType hasType, RenameClause renaming, ContractClause contracts, String comment) {
    this(featureNames,deferred,effective,redefined,arguments,hasType,renaming,contracts,comment, null);    
  }

  protected FeatureSpecification(List<String> featureNames, Boolean deferred, Boolean effective, Boolean redefined, List<FeatureArgument> arguments, HasType hasType, RenameClause renaming, ContractClause contracts, String comment, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.featureNames = featureNames; assert featureNames != null;
    this.deferred = deferred; assert deferred != null;
    this.effective = effective; assert effective != null;
    this.redefined = redefined; assert redefined != null;
    this.arguments = arguments; assert arguments != null;
    this.hasType = hasType; 
    this.renaming = renaming; 
    this.contracts = contracts; 
    this.comment = comment; 
    
  }
  
  public static FeatureSpecification mk(List<String> featureNames, Boolean deferred, Boolean effective, Boolean redefined, List<FeatureArgument> arguments, HasType hasType, RenameClause renaming, ContractClause contracts, String comment) {
    return new FeatureSpecification(featureNames, deferred, effective, redefined, arguments, hasType, renaming, contracts, comment);
  }

  public static FeatureSpecification mk(List<String> featureNames, Boolean deferred, Boolean effective, Boolean redefined, List<FeatureArgument> arguments, HasType hasType, RenameClause renaming, ContractClause contracts, String comment, SourceLocation location) {
    return new FeatureSpecification(featureNames, deferred, effective, redefined, arguments, hasType, renaming, contracts, comment, location);
  }

  // === Accessors ===

  public List<String> getFeatureNames() { return featureNames; }
  public Boolean getDeferred() { return deferred; }
  public Boolean getEffective() { return effective; }
  public Boolean getRedefined() { return redefined; }
  public List<FeatureArgument> getArguments() { return arguments; }
  public HasType getHasType() { return hasType; }
  public RenameClause getRenaming() { return renaming; }
  public ContractClause getContracts() { return contracts; }
  public String getComment() { return comment; }

  // === Others ===
  @Override
  public FeatureSpecification clone() {
    List<String> newFeatureNames = featureNames;
    Boolean newDeferred = deferred;
    Boolean newEffective = effective;
    Boolean newRedefined = redefined;
    List<FeatureArgument> newArguments = arguments;
    HasType newHasType = hasType == null ? null : hasType.clone();
    RenameClause newRenaming = renaming == null ? null : renaming.clone();
    ContractClause newContracts = contracts == null ? null : contracts.clone();
    String newComment = comment;
    
    return FeatureSpecification.mk(newFeatureNames, newDeferred, newEffective, newRedefined, newArguments, newHasType, newRenaming, newContracts, newComment, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("FeatureSpecification ast node: ");
    
    sb.append("featureNames = ");
    sb.append(featureNames);
    sb.append(", ");
    
    sb.append("deferred = ");
    sb.append(deferred);
    sb.append(", ");
    
    sb.append("effective = ");
    sb.append(effective);
    sb.append(", ");
    
    sb.append("redefined = ");
    sb.append(redefined);
    sb.append(", ");
    
    sb.append("arguments = ");
    sb.append(arguments);
    sb.append(", ");
    
    sb.append("hasType = ");
    sb.append(hasType);
    sb.append(", ");
    
    sb.append("renaming = ");
    sb.append(renaming);
    sb.append(", ");
    
    sb.append("contracts = ");
    sb.append(contracts);
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

