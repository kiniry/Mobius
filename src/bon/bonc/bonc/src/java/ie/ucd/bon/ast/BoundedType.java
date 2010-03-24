package ie.ucd.bon.ast;

import ie.ucd.bon.source.SourceLocation;

import java.util.List;

public class BoundedType extends Type {

  public final String binderIdentifier;
  
  public BoundedType(String binderIdentifier, String identifier, List<Type> actualGenerics, SourceLocation location) {
    super(identifier, actualGenerics, location);
    this.binderIdentifier = binderIdentifier;
  }

  public String getBinderIdentifier() {
    return binderIdentifier;
  }

  @Override
  public String toString() {
    return binderIdentifier + "==>" + super.toString();
  }
  
}
