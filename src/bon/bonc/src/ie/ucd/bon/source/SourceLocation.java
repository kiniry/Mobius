/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.source;

import java.io.File;

import org.antlr.runtime.CommonToken;
import org.antlr.runtime.Token;
import org.antlr.runtime.tree.CommonTree;

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
    this(t, t, sourceFile);
  }
  
  public SourceLocation(Token start, Token end, File sourceFile) {
    this.sourceFile = sourceFile;
    this.lineNumber = start.getLine();
    this.charPositionInLine = start.getCharPositionInLine();
    
    //System.out.println("SourceLoc from token: " + start.getText());
    
    if (start instanceof CommonToken) {
      CommonToken cToken = (CommonToken)start;
      this.absoluteCharPositionStart = cToken.getStartIndex();
      //System.out.println("Set absolute start: " + this.absoluteCharPositionStart);
    } else {
      //TODO Warn!
      System.out.println("Not CommonToken. " + start.getClass());
      this.absoluteCharPositionStart = -1;  
    }
    
    if (end instanceof CommonToken) {
      CommonToken cToken = (CommonToken)end;
      this.absoluteCharPositionEnd = cToken.getStopIndex();
      //System.out.println("Set absolute end: " + this.absoluteCharPositionEnd);
    } else {
      System.out.println("Not CommonToken. " + end.getClass());
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
