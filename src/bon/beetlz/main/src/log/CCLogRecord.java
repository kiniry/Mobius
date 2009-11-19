package log;

import java.util.logging.Level;
import java.util.logging.LogRecord;

import utils.BeetlzSourceLocation;

/**
 * A customized log record for recording errors found
 * in consistency checking.
 * SEVERE     - major inconsistency
 * WARNING    - minor inconsistency
 * INFO       - jml inconsistency
 * CONFIG     - files not found and similar
 * FINE       - information about what we are doing
 * FINER      - debug info
 * FINEST     - not assigned
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
@SuppressWarnings("serial")
public class CCLogRecord extends LogRecord implements Comparable < CCLogRecord > {
  /** Source location or the error.  */
  private final BeetlzSourceLocation my_sourceLoc;

  /**
   * Creare a new log record.
   * @param a_level level of this log record
   * @param a_source_location source location of this error, if no location
   * can be specified, null
   * @param a_message message of this error
   */
  public CCLogRecord(final Level a_level, final BeetlzSourceLocation a_source_location,
                     final String a_message) {
    super(a_level, a_message);
    this.my_sourceLoc = a_source_location;
  }


  /**
   * Get the source location in this log record.
   * @return source location
   */
  public final BeetlzSourceLocation getSourceLoc() {
    return my_sourceLoc;
  }



  /**
   *
   * @see java.lang.Object#toString()
   * @return string representation
   */
  @Override
  public final String toString() {
    return my_sourceLoc.toString() + getMessage();
  }


  /**
   * Compare two log records, so that they can be sorted.
   * Log records are sorted by location first, no-source records first,
   * then by messages alphabetically.
   * @see java.lang.Comparable#compareTo(java.lang.Object)
   * @param an_other log record to compare to
   * @return 0 if equal
   */
  @Override
  public int compareTo(final CCLogRecord an_other) {
    if (my_sourceLoc == null && an_other.my_sourceLoc != null) {
      return -1;
    } else if (my_sourceLoc != null && an_other.my_sourceLoc == null) {
      return 1;
    } else if (my_sourceLoc == null && an_other.my_sourceLoc == null) {
      if (this.getMessage().compareTo(an_other.getMessage()) != 0) {
        return this.getMessage().compareTo(an_other.getMessage());
      }
      return 0;
    } else if (my_sourceLoc.compareTo(an_other.my_sourceLoc) != 0) {
      return my_sourceLoc.compareTo(an_other.my_sourceLoc);
    }

    if (this.getMessage().compareTo(an_other.getMessage()) != 0) {
      return this.getMessage().compareTo(an_other.getMessage());
    }
    return 0;
  }

}
