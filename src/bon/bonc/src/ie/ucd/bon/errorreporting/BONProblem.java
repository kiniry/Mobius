/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.errorreporting;

import ie.ucd.bon.parser.SourceLocation;
import ie.ucd.bon.parser.SourceReader;

import java.io.File;
import java.io.PrintStream;

public abstract class BONProblem implements Comparable<BONProblem> {
  
  private static int creationID = 0;
  
  public static final int GENERAL_PROBLEM = -1;
  public static final int FILE_PROBLEM = -2;
  public static final int UNKNOWN_LINE = -3;
  public static final int EOF_LINE = -4;
  public static final int UNKNOWN_CHAR_POSITION = -5;
  
  public static final String STDIN_TEXT = "<stdin>";
  
  private final File sourceFile;
  private final int lineNumber;
  private final String sourceLine;
  private final int charPosition;
  
  private final int id;
  
  public BONProblem(File sourceFile, int lineNumber, int charPosition) {
    this.sourceFile = sourceFile;
    this.lineNumber = lineNumber;
    this.charPosition = charPosition;
    this.id = creationID++;
    
    this.sourceLine = getSourceLine();
  }
  
  public BONProblem(SourceLocation sourceLoc) {
    this(sourceLoc.getSourceFile(), sourceLoc.getLineNumber(), sourceLoc.getCharPosition());
  }
  
  private String getSourceLine() {
    if (lineNumber <= 0) {
      return null;
    }
    return SourceReader.getInstance().getSource(sourceFile, lineNumber);
  }
  
  public abstract boolean isError();
  public abstract boolean isWarning();
  
  public String getFileName() {
    return sourceFile.getName();
  }
  
  public String getFilePath(File file) {
    if (file == null) {
      return STDIN_TEXT;
    } else {
      return file.getPath();
    }
  }

  public int getLineNumber() {
    return lineNumber;
  }

  public int getCharPosition() {
    return charPosition;
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
    return this.getFileName().compareTo(o.getFileName());
  }
  
  private int compareLineNumber(final BONProblem o) {
    //Compare line number
    if (this.getLineNumber() == FILE_PROBLEM) {
      return o.getLineNumber() == FILE_PROBLEM ? 0 : -1;      
    } else if (o.getLineNumber() == FILE_PROBLEM) {
      return 1;
    } else if (this.getLineNumber() == UNKNOWN_LINE) {
      if (o.getLineNumber() == UNKNOWN_LINE) {
        return this.id - o.id;
      } else {
        return 1;
      }
    } else if (o.getLineNumber() == UNKNOWN_LINE) {
      return -1;
    } else if (o.getLineNumber() == EOF_LINE) {
      return 1;
    } else {
      return this.getLineNumber() - o.getLineNumber();      
    }
  }
  
  private int compareCharacterPosition(final BONProblem o) {
    //Compare character position
    if (this.getCharPosition() == UNKNOWN_CHAR_POSITION) {
      return o.getCharPosition() == UNKNOWN_CHAR_POSITION ? 0 : -1;      
    } else if (o.getCharPosition() == UNKNOWN_CHAR_POSITION) {
      return 1;
    } else {
      return this.getCharPosition() - o.getCharPosition();
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
        ps.print(STDIN_TEXT);
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
    if (charPosition >= 0 && sourceLine != null) {
      
      int tabCount = 0;
      StringBuilder sb = new StringBuilder();
      for (int i=0; i < sourceLine.length(); i++) {
        char c = sourceLine.charAt(i);
        if (c == '\t') {
          sb.append("  ");
          if (i < charPosition) {
            tabCount++;
          }
        } else {
          sb.append(c);
        }
      }
      
      ps.println(sb.toString());
      
      ps.println(getErrorPosition(charPosition + tabCount));
    }
  }

  public boolean equals(Object obj) {
    if (!(obj instanceof BONProblem)) {
      return false;
    }
    BONProblem other = (BONProblem)obj;
    return this.lineNumber == other.lineNumber && this.charPosition == other.charPosition && this.sourceFile.equals(other.sourceFile) && this.getMessage().equals(other.getMessage());
  }
  
  public int hashCode() {
    return this.sourceFile.hashCode() + (this.lineNumber*1024) + this.charPosition + this.getMessage().hashCode();
  }
  
}
