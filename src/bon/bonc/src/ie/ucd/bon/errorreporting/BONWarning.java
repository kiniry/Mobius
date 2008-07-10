/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.errorreporting;

import ie.ucd.bon.source.SourceLocation;

import java.io.File;
import java.io.PrintStream;

public abstract class BONWarning extends BONProblem {

//  public BONWarning(File sourceFile, int lineNumber, int charPosition) {
//    super(sourceFile, lineNumber, charPosition);
//  }

  public BONWarning(SourceLocation sourceLoc) {
    super(sourceLoc);
  }
  
  @Override
  public final boolean isError() {
    return false;
  }

  @Override
  public final boolean isWarning() {
    return true;
  }

  @Override
  protected void printMessage(PrintStream ps) {
    ps.print("Warning: ");
    super.printMessage(ps);
  }  
  
  
}
