package genericutils;

import java.util.logging.*;

/**
 * Print each message on exactly one line.
 */
public class OneLineLogFormatter extends Formatter {
  private StringBuilder sb;

  public OneLineLogFormatter() {
    sb = new StringBuilder();
  }

  @Override
  public String format(LogRecord record) {
    sb.setLength(0);
    sb.append(record.getLevel().toString());
    sb.append(" (");
    sb.append(record.getLoggerName());
    sb.append("): "); // not sad
    sb.append(record.getMessage());
    sb.append("\n");
    return sb.toString();
  }
}
