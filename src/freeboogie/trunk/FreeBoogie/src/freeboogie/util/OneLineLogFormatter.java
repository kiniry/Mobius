package freeboogie.util;

import java.util.logging.*;

public class OneLineLogFormatter extends Formatter {
  @Override
  public String format(LogRecord record) {
    return "" + record.getLevel() + ": " + record.getMessage() + "\n";
  }
}
