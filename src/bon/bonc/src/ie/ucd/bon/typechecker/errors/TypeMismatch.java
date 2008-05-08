/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import java.io.File;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class TypeMismatch extends TypeCheckingError {

  private static final String message = "Type mismatch. Found %s, required %s";

  private final String actualType;
  private final String desiredType;
  
  public TypeMismatch(File sourceFile, int lineNumber, int charPosition, String actualType, String desiredType) {
    super(sourceFile, lineNumber, charPosition);
    this.actualType = actualType;
    this.desiredType = desiredType;
  }

  public TypeMismatch(SourceLocation loc, String actualType, String desiredType) {
    super(loc);
    this.actualType = actualType;
    this.desiredType = desiredType;
  }

  @Override
  public String getMessage() {
    return String.format(message, actualType, desiredType);
  }
  
  

}
