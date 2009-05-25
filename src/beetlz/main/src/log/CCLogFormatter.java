package log;

import java.util.logging.Formatter;
import java.util.logging.LogRecord;

/**
 * Formats log records.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class CCLogFormatter extends Formatter {

  /**
   * Format a given log record.
   * @see java.util.logging.Formatter#format(java.util.logging.LogRecord)
   * @param a_record record to format
   * @return formated string
   */
  @Override
  public final String format(final LogRecord a_record) {
    if (a_record instanceof CCLogRecord) {
      final CCLogRecord rec = (CCLogRecord) a_record;
      String mssg = ""; //$NON-NLS-1$
      if (rec.getSourceLoc() != null) {
        mssg += rec.getSourceLoc().getConciseSourceLocation() + ": "; //$NON-NLS-1$
      }
      mssg += rec.getMessage() + "\n"; //$NON-NLS-1$
      return mssg;
    } else {
      return a_record.getMessage() + "\n";  //$NON-NLS-1$
    }

  }



}
