/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.util.StringUtil;

import java.util.List;

public class DeferredFeatureInNonDeferredClassError extends TypeCheckingError {

  private static final String message1 = "Deferred feature %s declared in non-deferred class %s";
  private static final String message2 = "Deferred features %s declared in non-deferred class %s";
  
  private final String message;
  
  public DeferredFeatureInNonDeferredClassError(SourceLocation loc,
      String featureNames, boolean moreThanOneFeature, String className) {
    super(loc);
    
    this.message = moreThanOneFeature ? 
        String.format(message2, featureNames, className) 
      : String.format(message1, featureNames, className);
  }
  
  public DeferredFeatureInNonDeferredClassError(SourceLocation loc,
      List<String> featureNames, String className) {
    super(loc);
    
    if (featureNames.size() == 1) {
      this.message = String.format(message1, featureNames.get(0), className);
    } else {
      this.message = String.format(message2, StringUtil.appendWithSeparator(featureNames, ", "), className);
    } 
  }
  

  @Override
  public String getMessage() {
    return message;
  }

}
