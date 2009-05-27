/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

import java.io.File;

public class NameNotUniqueError extends TypeCheckingError {

  private static final String message = "%s identifier %s is not unique (other use: %s %s - %s:%s)";
  
  private final String type;
  private final String name;
  private final String otherUseType;
  private final File otherUseFile;
  private final int otherUseLineNumber;

  public NameNotUniqueError(SourceLocation loc, String type, String name,
      String otherUseType, SourceLocation otherUseLoc) {
    super(loc);
    this.type = type;
    this.name = name;
    this.otherUseType = otherUseType;
    this.otherUseFile = otherUseLoc.getSourceFile();
    this.otherUseLineNumber = otherUseLoc.getLineNumber();
  }

  @Override
  public String getMessage() {
    return String.format(message, type, name, otherUseType, name, SourceLocation.getFilePath(otherUseFile), otherUseLineNumber);
  }

}
