/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.source;

import java.io.File;

import org.antlr.runtime.Token;

public class SourceLocation {

  private final File sourceFile;
  private final int lineNumber;
  private final int charPosition;
  
  public SourceLocation(File sourceFile, int lineNumber, int charPosition) {
    this.sourceFile = sourceFile;
    this.lineNumber = lineNumber;
    this.charPosition = charPosition;
  }
  
  public SourceLocation(Token t, File sourceFile) {
    this(sourceFile, t.getLine(), t.getCharPositionInLine());
  }

  public File getSourceFile() {
    return sourceFile;
  }
  
  public String getSourceFilePath() {
    return sourceFile != null ? sourceFile.getPath() : "stdin";
  }

  public int getLineNumber() {
    return lineNumber;
  }

  public int getCharPosition() {
    return charPosition;
  }

  @Override
  public String toString() {
    return "File: " + (sourceFile!=null ? sourceFile.getPath() : "stdin") + ", line: " + lineNumber + ", char: " + charPosition;
  } 
  
  
  
}
