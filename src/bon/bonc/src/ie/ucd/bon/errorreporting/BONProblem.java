/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.errorreporting;

import ie.ucd.bon.source.SourceLineReader;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.source.SourceReader;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

public abstract class BONProblem implements Comparable<BONProblem> {
  
  private static int creationID = 0;
  
  public static final int GENERAL_PROBLEM = -1;
  public static final int FILE_PROBLEM = -2;
  public static final int UNKNOWN_LINE = -3;
  public static final int EOF_LINE = -4;
  public static final int UNKNOWN_CHAR_POSITION = -5;
  
    private final File sourceFile;
    private final int lineNumber;
    private final String sourceLine;
    private final int charPositionInLine;
//  private final int length;
  
  private final SourceLocation location;
  
  private final int id;
  
//  public BONProblem(File sourceFile, int lineNumber, int charPosition) {
//    this(sourceFile, lineNumber, charPosition, 1);
//  }
//  
//  public BONProblem(File sourceFile, int lineNumber, int charPosition, int length) {
//    this.sourceFile = sourceFile;
//    this.lineNumber = lineNumber;
//    this.charPosition = charPosition;
//    this.length = length;
//    this.id = creationID++;
//    
//    this.sourceLine = getSourceLine();
//  }
  
  public BONProblem(SourceLocation sourceLoc) {
    this.location = sourceLoc;
    
    this.charPositionInLine = sourceLoc.getCharPositionInLine();
    this.lineNumber = sourceLoc.getLineNumber();
    this.sourceFile = sourceLoc.getSourceFile();
    
    this.id = creationID++;
    
    this.sourceLine = getSourceLine();
  }
  
  private String getSourceLine() {
    if (lineNumber <= 0) {
      return null;
    }
    return SourceReader.getInstance().getSource(sourceFile, lineNumber);
  }
  
  public abstract boolean isError();
  public abstract boolean isWarning();
  
//  public String getFileName() {
//    return sourceFile == null ? null : sourceFile.getName();
//  }
  
  
  
//  public File getFile() {
//    return sourceFile;
//  }


  public SourceLocation getLocation() {
    return location;
  }

  public abstract String getMessage();

  public int compareTo(final BONProblem o) {
    
    int fileCompare = this.compareFile(o);
    if (fileCompare != 0) {
      return fileCompare;
    }
    
    int lineNumberCompare = this.compareLineNumber(o);
    if (lineNumberCompare != 0) {
      return lineNumberCompare;
    }
    
    int charPositionCompare = this.compareCharacterPosition(o);
    if (charPositionCompare != 0) {
      return charPositionCompare;
    }
    
    return this.getClass().equals(o.getClass()) ? 0 : -1;
  }  
  
  private int compareFile(final BONProblem o) {
    //General errors not involving a specific file...
    if (sourceFile == null) {
      return o.sourceFile == null ? 0 : -1;
    } else if (o.sourceFile == null) {
      return 1;
    }
    
    //Compare file name
    return this.getLocation().getFileName().compareTo(o.getLocation().getFileName());
  }
  
  private int compareLineNumber(final BONProblem o) {
    //Compare line number
    if (this.location.getLineNumber() == FILE_PROBLEM) {
      return o.location.getLineNumber() == FILE_PROBLEM ? 0 : -1;      
    } else if (o.location.getLineNumber() == FILE_PROBLEM) {
      return 1;
    } else if (this.location.getLineNumber() == UNKNOWN_LINE) {
      if (o.location.getLineNumber() == UNKNOWN_LINE) {
        return this.id - o.id;
      } else {
        return 1;
      }
    } else if (o.location.getLineNumber() == UNKNOWN_LINE) {
      return -1;
    } else if (o.location.getLineNumber() == EOF_LINE) {
      return 1;
    } else {
      return this.location.getLineNumber() - o.location.getLineNumber();      
    }
  }
  
  private int compareCharacterPosition(final BONProblem o) {
    //Compare character position
    if (this.location.getCharPositionInLine() == UNKNOWN_CHAR_POSITION) {
      return o.location.getCharPositionInLine() == UNKNOWN_CHAR_POSITION ? 0 : -1;      
    } else if (o.location.getCharPositionInLine() == UNKNOWN_CHAR_POSITION) {
      return 1;
    } else {
      return this.location.getCharPositionInLine() - o.location.getCharPositionInLine();
    }
  }
  
  
  /**
   * Returns a String which simply contains a caret character to indicate the location of
   * the error.
   * @param re The RecognitionException representing the error.
   * @return A String to indicate the position of the error.
   */
  private String getErrorPosition(int caretPosition) {
    StringBuilder sb = new StringBuilder();
    for (int i=0; i < caretPosition; i++) {
      sb.append(' ');
    }
    sb.append('^');
    return sb.toString();
  }
  
  public void print(PrintStream ps) {
    printStart(ps);
    printMessage(ps);
    printSourcePosition(ps);
  }
  
  protected void printStart(PrintStream ps) {
    if (sourceFile == null) {
      if (lineNumber > 0) {
        ps.print(SourceLocation.STDIN_TEXT);
        ps.print(":");
      } else {
        return;
      }        
    } else {
      ps.print(sourceFile.getPath());
      ps.print(':');
    }
    if (lineNumber > 0) {
      ps.print(lineNumber);
      ps.print(": ");
    } else {
      ps.print(' ');
    }
  }
  
  protected void printMessage(PrintStream ps) {
    ps.println(getMessage());
  }
  
  protected void printSourcePosition(PrintStream ps) {
    if (charPositionInLine >= 0 && sourceLine != null) {
      
      int tabCount = 0;
      StringBuilder sb = new StringBuilder();
      for (int i=0; i < sourceLine.length(); i++) {
        char c = sourceLine.charAt(i);
        if (c == '\t') {
          sb.append("  ");
          if (i < charPositionInLine) {
            tabCount++;
          }
        } else {
          sb.append(c);
        }
      }
      
      ps.println(sb.toString());
      
      ps.println(getErrorPosition(charPositionInLine + tabCount));
    }
  }

  public boolean equals(Object obj) {
    if (!(obj instanceof BONProblem)) {
      return false;
    }
    BONProblem other = (BONProblem)obj;
    return this.lineNumber == other.lineNumber && this.charPositionInLine == other.charPositionInLine && this.sourceFile.equals(other.sourceFile) && this.getMessage().equals(other.getMessage());
  }
  
  public int hashCode() {
    return this.sourceFile.hashCode() + (this.lineNumber*1024) + this.charPositionInLine + this.getMessage().hashCode();
  }
  
}
