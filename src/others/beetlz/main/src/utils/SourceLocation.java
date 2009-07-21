/**
 * Package of utility classes.
 */
package utils;

import java.io.File;

/**
 * This class stores where the feature is located in the source file.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class SourceLocation implements Comparable < SourceLocation > {
  /** Representation of the file where the error is.  */
  private final File my_sourceFile;
  /** Line number in the file where error is. */
  private final int my_lineNumber;

  /**
   * Default implementation of SourceLocation denoting no specific location,
   * that is, it denotes the whole system.
   */
  public SourceLocation() {
    this.my_sourceFile = new File(""); //$NON-NLS-1$
    this.my_lineNumber = -1;
  }

  /**
   * Creates a new SourceLocation.
   * @param a_source_file if no file specifiable, give a file with empty string file name
   * @param a_line_number if -1, no line number specifiable
   */
  public SourceLocation(/*@ non_null @*/final File a_source_file,
                        final int a_line_number) {
    this.my_sourceFile = a_source_file;
    if (a_source_file.getAbsolutePath().equals("")) { //$NON-NLS-1$
      this.my_lineNumber = -1;
    } else {
      this.my_lineNumber = a_line_number;
    }
  }

  /**
   * @return the sourceFile (may be null)
   */
  public final File getSourceFile() {
    return this.my_sourceFile;
  }

  /**
   * Get the name of the source file.
   * Since we allow a 'null' source file, this method will save us from
   * NullPointerExceptions.
   * @return 'null' if source file not specifiable, otherwise name of source file.
   */
  public final String getSourceFileName() {
    return this.my_sourceFile.getName();
  }

  /**
   * Get the line number.
   * @return -1 if line number not specifiable, otherwise line number
   */
  public final int getLineNumber() {
    return this.my_lineNumber;
  }

  /**
   * Whether this source location belongs to a Java or JML file.
   * @return true if this source location is in a Java or JML file
   */
  public final boolean isJavaFile() {
    final String s = my_sourceFile.getName();
    return (s.endsWith(".java"));  //$NON-NLS-1$

  }

  /**
   * Compares based on source file name and line number.
   * Non-existent valued source files are sorted first.
   * @see java.lang.Comparable#compareTo(java.lang.Object)
   * @param an_other SourceLocation object to be compared to
   * @return 0 if equal
   */
  @Override
  public final int compareTo(final SourceLocation an_other) {
    if (an_other == null) {
      return 1;
    }

    if (this.getSourceFileName() != an_other.getSourceFileName()) {
      if (this.getSourceFileName().equals(BConst.NULL_SMARTSTRING)) {
        return -1;
      }
      if (an_other.getSourceFileName().equals(BConst.NULL_SMARTSTRING)) {
        return 1;
      }
      return this.getSourceFileName().compareTo(an_other.getSourceFileName());
    } else if (this.getLineNumber() != an_other.getLineNumber()) {
      if (this.getLineNumber() < an_other.getLineNumber()) {
        return -1;
      } else {
        return 1;
      }
    } else {
      return 0;
    }

  }

  /**
   * String representation.
   * @see java.lang.Object#toString()
   * @return string representation
   */
  @Override
  public final String toString() {
    return "file " + getSourceFileName() + ", line: " + //$NON-NLS-1$ //$NON-NLS-2$
    getLineNumber();
  }

  /**
   * Does this source location actually exists,
   * it may not exist, for example for a class-not-found
   * error. In that case, the associated file path is
   * zero-length.
   * @return true if source location exists
   */
  public final boolean exists() {
    return (my_sourceFile.getAbsolutePath().length() > 0);
  }

  /**
   * Short string representation of this source location.
   * @return short string (one line)
   */
  public final String getConciseSourceLocation() {
    if (!exists()) {
      return ""; //$NON-NLS-1$
    }
    return my_sourceFile.getName() + ":" + my_lineNumber; //$NON-NLS-1$
  }

  /**
   * Generates a hash code based on line number
   * and file name.
   * @see java.lang.Object#hashCode()
   * @return hash code
   */
  @Override
  public final int hashCode() {
    final int prime = 31;
    final int sevenPrime = 7;
    int result = sevenPrime;
    result = prime * sevenPrime + my_lineNumber;
    result = prime * sevenPrime + this.getSourceFileName().hashCode();
    return result;
  }

  /**
   * Compares two source locations.
   * @see java.lang.Object#equals(java.lang.Object)
   * @param an_other object to compare to
   * @return true if the two objects are equal
   */
  @Override
  public final boolean equals(final Object an_other) {
    if (this == an_other) {
      return true;
    }
    if ((an_other == null) || (an_other.getClass() != this.getClass())) {
      return false;
    }
    final SourceLocation a_string = (SourceLocation) an_other;
    if (this.compareTo(a_string) == 0) {
      return true;
    }
    return false;
  }

}
