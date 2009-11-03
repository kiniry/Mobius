package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;

public class ParentFeatureMustBeDeferred extends TypeCheckingError {

  private static final String MESSAGE = "Feature %s cannot be effective, as %s in parent class %s is not deferred.";
  private final String message;
  
  public ParentFeatureMustBeDeferred(SourceLocation sourceLoc, String featureName, String parentClassName) {
    super(sourceLoc);
    message = String.format(MESSAGE, featureName, featureName, parentClassName);
  }

  @Override
  public String getMessage() {
    return message;
  }

}
