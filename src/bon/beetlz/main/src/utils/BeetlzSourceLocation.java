/**
 * Package of utility classes.
 */
package utils;

import ie.ucd.bon.source.SourceLocation;

import java.io.File;

/**
 * This class stores where the feature is located in the source file.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class BeetlzSourceLocation extends SourceLocation {

  private final boolean isJava;
  
  /**
   * Default implementation of SourceLocation denoting no specific location,
   * that is, it denotes the whole system.
   */
  public BeetlzSourceLocation(boolean isJava) {
    super(NO_LOCATION);
    this.isJava = isJava;
  }
  
  public BeetlzSourceLocation(SourceLocation a_loc) {
    super(a_loc);
    this.isJava = false;
  }

  /**
   * Creates a new SourceLocation.
   * @param a_source_file if no file specifiable, give a file with empty string file name
   * @param a_line_number if -1, no line number specifiable
   */
  public BeetlzSourceLocation(/*@ non_null @*/final File a_source_file, final int a_line_number, boolean isJava) {
    super(a_source_file, a_line_number, UNKNOWN, UNKNOWN, UNKNOWN);
    this.isJava = isJava;
  }

  public BeetlzSourceLocation(File sourceFile, int lineNumber, int charPositionInLine, int absoluteCharPositionStart,
      int absoluteCharPositionEnd, boolean isJava) {
    super(sourceFile, lineNumber, charPositionInLine, absoluteCharPositionStart, absoluteCharPositionEnd);
    this.isJava = isJava;
  }

  /**
   * Whether this source location belongs to a Java or JML file.
   * @return true if this source location is in a Java or JML file
   */
  public final boolean isJavaFile() {
    return isJava;  //$NON-NLS-1$

  }

  /**
   * String representation.
   * @see java.lang.Object#toString()
   * @return string representation
   */
  public final String toFileAndLineString() {
    return "file " + getFileName() + ", line: " + //$NON-NLS-1$ //$NON-NLS-2$
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
    return getSourceFile() == null ? false : (getSourceFile().getAbsolutePath().length() > 0);
  }

  /**
   * Short string representation of this source location.
   * @return short string (one line)
   */
  public final String getConciseSourceLocation() {
    if (!exists()) {
      return ""; //$NON-NLS-1$
    }
    return getSourceFile().getName() + ":" + getLineNumber(); //$NON-NLS-1$
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
    result = prime * sevenPrime + getLineNumber();
    result = prime * sevenPrime + getSourceFile().hashCode();
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
