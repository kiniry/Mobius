package java.util.logging;

import java.io.*;
import java.text.*;
import java.util.Date;

public class SimpleFormatter extends Formatter {
    
    public SimpleFormatter() {
        
    }
    Date dat = new Date();
    private static final String format = "{0,date} {0,time}";
    private MessageFormat formatter;
    private Object[] args = new Object[1];
    private String lineSeparator = (String)(String)java.security.AccessController.doPrivileged(new sun.security.action.GetPropertyAction("line.separator"));
    
    public synchronized String format(LogRecord record) {
        StringBuffer sb = new StringBuffer();
        dat.setTime(record.getMillis());
        args[0] = dat;
        StringBuffer text = new StringBuffer();
        if (formatter == null) {
            formatter = new MessageFormat(format);
        }
        formatter.format(args, text, null);
        sb.append(text);
        sb.append(" ");
        if (record.getSourceClassName() != null) {
            sb.append(record.getSourceClassName());
        } else {
            sb.append(record.getLoggerName());
        }
        if (record.getSourceMethodName() != null) {
            sb.append(" ");
            sb.append(record.getSourceMethodName());
        }
        sb.append(lineSeparator);
        String message = formatMessage(record);
        sb.append(record.getLevel().getLocalizedName());
        sb.append(": ");
        sb.append(message);
        sb.append(lineSeparator);
        if (record.getThrown() != null) {
            try {
                StringWriter sw = new StringWriter();
                PrintWriter pw = new PrintWriter(sw);
                record.getThrown().printStackTrace(pw);
                pw.close();
                sb.append(sw.toString());
            } catch (Exception ex) {
            }
        }
        return sb.toString();
    }
}
