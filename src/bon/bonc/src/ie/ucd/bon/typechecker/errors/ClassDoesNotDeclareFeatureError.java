/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;

public class ClassDoesNotDeclareFeatureError extends TypeCheckingError {

  private static final String message = "Class %s does not declare a feature with name %s";
  
  private final String className;
  private final String featureName;

  public ClassDoesNotDeclareFeatureError(SourceLocation loc, String className, String featureName) {
    super(loc);
    this.className = className;
    this.featureName = featureName;
  }

  @Override
  public String getMessage() {
    return String.format(message, className, featureName);
  }  

}
