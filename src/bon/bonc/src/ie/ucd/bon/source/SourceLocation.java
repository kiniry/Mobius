/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.source;

import java.io.File;

import org.antlr.runtime.CommonToken;
import org.antlr.runtime.Token;

public class SourceLocation implements Comparable<SourceLocation> {

	public static final int GENERAL_PROBLEM = -1;
	public static final int FILE_PROBLEM = -2;
	public static final int UNKNOWN_LINE = -3;
	public static final int EOF_LINE = -4;
	public static final int UNKNOWN_CHAR_POSITION = -5;

	public static final String STDIN_TEXT = "<stdin>";

	private final File sourceFile;
	private int lineNumber;
	private int charPositionInLine;

	private int absoluteCharPositionStart;
	private int absoluteCharPositionEnd;

	public SourceLocation(File sourceFile, int lineNumber,
			int charPositionInLine, int absoluteCharPositionStart,
			int absoluteCharPositionEnd
	) {
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
		//System.out.println("start token: " + start);
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
	
	public void setStartToken(Token start) {
	  this.lineNumber = start.getLine();
	  this.charPositionInLine = start.getCharPositionInLine();
	  if (start instanceof CommonToken) {
	    this.absoluteCharPositionStart = ((CommonToken)start).getStartIndex();
	  } else {
	    this.absoluteCharPositionStart = -1;
	  }
	}
	
	public void setEndToken(Token end) {
    if (end instanceof CommonToken) {
      this.absoluteCharPositionEnd = ((CommonToken)end).getStopIndex();
    } else {
      this.absoluteCharPositionEnd = -1;
    }
  }

	public final File getSourceFile() {
		return sourceFile;
	}

	public final String getSourceFilePath() {
		return sourceFile != null ? sourceFile.getPath() : "stdin";
	}

	public final String getFileName() {
		return sourceFile == null ? null : sourceFile.getName();
	}

	public final int getLineNumber() {
		return lineNumber;
	}

	public final int getCharPositionInLine() {
		return charPositionInLine;
	}

	public final int getAbsoluteCharPositionStart() {
		return absoluteCharPositionStart;
	}

	public final int getAbsoluteCharPositionEnd() {
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

	@Override
	public boolean equals(Object obj) {
	  if (!(obj instanceof SourceLocation)) {
	    return false;
	  }
	  SourceLocation other = (SourceLocation)obj;
	  if (this.sourceFile != null && !this.sourceFile.equals(other.sourceFile)) {
	    return false;
	  }
		return this.lineNumber == other.lineNumber && this.charPositionInLine == other.charPositionInLine 
		       && this.absoluteCharPositionStart == other.absoluteCharPositionStart 
		       && this.absoluteCharPositionEnd == other.absoluteCharPositionEnd;
	}

	public int compareTo(SourceLocation o) {
	  if (o == null) {
	    return 1;
	  }
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

		return 0;
	}


	private int compareFile(final SourceLocation o) {
		//General errors not involving a specific file...
		if (sourceFile == null) {
			return o.sourceFile == null ? 0 : -1;
		} else if (o.sourceFile == null) {
			return 1;
		}

		//Compare file name
		return this.getFileName().compareTo(o.getFileName());
	}

	private int compareLineNumber(final SourceLocation o) {
		//Compare line number
		if (this.getLineNumber() == FILE_PROBLEM) {
			return o.getLineNumber() == FILE_PROBLEM ? 0 : -1;      
		} else if (o.getLineNumber() == FILE_PROBLEM) {
			return 1;
		} else if (this.getLineNumber() == UNKNOWN_LINE) {
			if (o.getLineNumber() == UNKNOWN_LINE) {
				return 0;
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

	private int compareCharacterPosition(final SourceLocation o) {
		//Compare character position
		if (this.getCharPositionInLine() == UNKNOWN_CHAR_POSITION) {
			return o.getCharPositionInLine() == UNKNOWN_CHAR_POSITION ? 0 : -1;      
		} else if (o.getCharPositionInLine() == UNKNOWN_CHAR_POSITION) {
			return 1;
		} else {
			return this.getCharPositionInLine() - o.getCharPositionInLine();
		}
	}

  @Override
  public int hashCode() {
    return this.sourceFile.hashCode() + (this.lineNumber*1024*1024) + (this.absoluteCharPositionStart*1024) + this.charPositionInLine;
  }

	
	
}
