/** Public domain. */

package freeboogie.ast;

/**
 * Represents a known or unknown file location.
 *  
 * @author rgrig 
 * @author reviewed by TODO
 */
public class Location {
  private String file;
  private int line, column;

  /** Creates an `unknown' location. */
  public Location() {
    file = null;
  }
  
  /** Creates a location from position info.
   * @param file_ The file name, preferably in full path.
   * @param line_ The line number, starting from 1.
   * @param column_ The column number, starting from 1 and 
   *                counting tabs as one char.
   */
  //@ requires file != null ==> line_ > 0;
  //@ requires file != null ==> column_ > 0;
  public Location(String file_, int line_, int column_) {
    file = file_;
    line = line_;
    column = column_;
  }
  
  /** @return Returns whether this is a known file position. */
  public boolean isKnown() {
    return file != null;
  }
  
  /** @return Returns the column. */
  public int getColumn() {
    return column;
  }

  /** @return Returns the file. */
  public String getFile() {
    return file;
  }

  /** @return Returns the line. */
  public int getLine() {
    return line;
  }
  

  /**
   * Illustrates usage.
   * @param args Unused.
   */
  public static void main(String[] args) {
    Location unknown = new Location();
    assert !unknown.isKnown();
    unknown = new Location(null, 1, -1);
    assert !unknown.isKnown();
    
    String file = "bau";
    int line = 28743;
    int col = 912374; 
    Location known = new Location(file, line, col);
    assert known.isKnown();
    assert file.equals(known.getFile());
    assert line == known.getLine();
    assert col == known.getColumn();
  }
}
