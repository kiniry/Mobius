/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.source;

import java.io.File;

import org.antlr.runtime.CommonToken;
import org.antlr.runtime.Token;

public class SourceLocation {

  public static final String STDIN_TEXT = "<stdin>";
  
  private final File sourceFile;
  private final int lineNumber;
  private final int charPositionInLine;
  
  private final int absoluteCharPositionStart;
  private final int absoluteCharPositionEnd;
  
  public SourceLocation(File sourceFile, int lineNumber,
      int charPositionInLine, int absoluteCharPositionEnd,
      int absoluteCharPositionStart) {
    this.sourceFile = sourceFile;
    this.lineNumber = lineNumber;
    this.charPositionInLine = charPositionInLine;
    this.absoluteCharPositionEnd = absoluteCharPositionEnd;
    this.absoluteCharPositionStart = absoluteCharPositionStart;
  }

  public SourceLocation(Token t, File sourceFile) {
    this.sourceFile = sourceFile;
    this.lineNumber = t.getLine();
    this.charPositionInLine = t.getCharPositionInLine();
    
    if (t instanceof CommonToken) {
      CommonToken cToken = (CommonToken)t;
      this.absoluteCharPositionStart = cToken.getStartIndex();
      this.absoluteCharPositionEnd = cToken.getStopIndex();
    } else {
      //TODO Warn!
      this.absoluteCharPositionStart = -1;
      this.absoluteCharPositionEnd = -1;
    }
  }
  
  public SourceLocation(Token start, Token end, File sourceFile) {
    this.sourceFile = sourceFile;
    this.lineNumber = start.getLine();
    this.charPositionInLine = start.getCharPositionInLine();
    
    if (start instanceof CommonToken) {
      CommonToken cToken = (CommonToken)start;
      this.absoluteCharPositionStart = cToken.getStartIndex();
    } else {
      //TODO Warn!
      this.absoluteCharPositionStart = -1;  
    }
    
    if (end instanceof CommonToken) {
      CommonToken cToken = (CommonToken)end;
      this.absoluteCharPositionEnd = cToken.getStopIndex(); 
    } else {
      this.absoluteCharPositionEnd = -1;  
    }
  }

  public File getSourceFile() {
    return sourceFile;
  }
  
  public String getSourceFilePath() {
    return sourceFile != null ? sourceFile.getPath() : "stdin";
  }

  public String getFileName() {
    return sourceFile == null ? null : sourceFile.getName();
  }
  
  public int getLineNumber() {
    return lineNumber;
  }

  public int getCharPositionInLine() {
    return charPositionInLine;
  }

  public int getAbsoluteCharPositionStart() {
    return absoluteCharPositionStart;
  }

  public int getAbsoluteCharPositionEnd() {
    return absoluteCharPositionEnd;
  }

  @Override
  public String toString() {
    return "File: " + (sourceFile!=null ? sourceFile.getPath() : "stdin") + ", line: " + lineNumber + ", char: " + charPositionInLine;
  } 
  
  public String getFilePath() {
    return getFilePath(sourceFile);
  }
  
  public static String getFilePath(File file) {
    if (file == null) {
      return STDIN_TEXT;
    } else {
      return file.getPath();
    }
  }
  
}
