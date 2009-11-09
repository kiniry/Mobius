package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;

public class ParentFeatureIsDeferredError extends TypeCheckingError {

  private static final String MESSAGE = "Feature %s is redefined, but feature %s in parent class %s is deferred.";
  private final String message;

  public ParentFeatureIsDeferredError(SourceLocation sourceLoc, String featureName, String parentName) {
    super(sourceLoc);
    message = String.format(MESSAGE, featureName, featureName, parentName);
  }

  @Override
  public String getMessage() {
    return message;
  }

}
