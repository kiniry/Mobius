package java.util.logging;

import java.io.*;
import java.nio.charset.Charset;
import java.util.*;

public class XMLFormatter extends Formatter {
    
    public XMLFormatter() {
        
    }
    private LogManager manager = LogManager.getLogManager();
    
    private void a2(StringBuffer sb, int x) {
        if (x < 10) {
            sb.append('0');
        }
        sb.append(x);
    }
    
    private void appendISO8601(StringBuffer sb, long millis) {
        Date date = new Date(millis);
        sb.append(date.getYear() + 1900);
        sb.append('-');
        a2(sb, date.getMonth() + 1);
        sb.append('-');
        a2(sb, date.getDate());
        sb.append('T');
        a2(sb, date.getHours());
        sb.append(':');
        a2(sb, date.getMinutes());
        sb.append(':');
        a2(sb, date.getSeconds());
    }
    
    private void escape(StringBuffer sb, String text) {
        if (text == null) {
            text = "<null>";
        }
        for (int i = 0; i < text.length(); i++) {
            char ch = text.charAt(i);
            if (ch == '<') {
                sb.append("&lt;");
            } else if (ch == '>') {
                sb.append("&gt;");
            } else if (ch == '&') {
                sb.append("&amp;");
            } else {
                sb.append(ch);
            }
        }
    }
    
    public String format(LogRecord record) {
        StringBuffer sb = new StringBuffer(500);
        sb.append("<record>\n");
        sb.append("  <date>");
        appendISO8601(sb, record.getMillis());
        sb.append("</date>\n");
        sb.append("  <millis>");
        sb.append(record.getMillis());
        sb.append("</millis>\n");
        sb.append("  <sequence>");
        sb.append(record.getSequenceNumber());
        sb.append("</sequence>\n");
        String name = record.getLoggerName();
        if (name != null) {
            sb.append("  <logger>");
            escape(sb, name);
            sb.append("</logger>\n");
        }
        sb.append("  <level>");
        escape(sb, record.getLevel().toString());
        sb.append("</level>\n");
        if (record.getSourceClassName() != null) {
            sb.append("  <class>");
            escape(sb, record.getSourceClassName());
            sb.append("</class>\n");
        }
        if (record.getSourceMethodName() != null) {
            sb.append("  <method>");
            escape(sb, record.getSourceMethodName());
            sb.append("</method>\n");
        }
        sb.append("  <thread>");
        sb.append(record.getThreadID());
        sb.append("</thread>\n");
        if (record.getMessage() != null) {
            String message = formatMessage(record);
            sb.append("  <message>");
            escape(sb, message);
            sb.append("</message>");
            sb.append("\n");
        }
        ResourceBundle bundle = record.getResourceBundle();
        try {
            if (bundle != null && bundle.getString(record.getMessage()) != null) {
                sb.append("  <key>");
                escape(sb, record.getMessage());
                sb.append("</key>\n");
                sb.append("  <catalog>");
                escape(sb, record.getResourceBundleName());
                sb.append("</catalog>\n");
            }
        } catch (Exception ex) {
        }
        Object[] parameters = record.getParameters();
        if (parameters != null && parameters.length != 0 && record.getMessage().indexOf("{") == -1) {
            for (int i = 0; i < parameters.length; i++) {
                sb.append("  <param>");
                try {
                    escape(sb, parameters[i].toString());
                } catch (Exception ex) {
                    sb.append("???");
                }
                sb.append("</param>\n");
            }
        }
        if (record.getThrown() != null) {
            Throwable th = record.getThrown();
            sb.append("  <exception>\n");
            sb.append("    <message>");
            escape(sb, th.toString());
            sb.append("</message>\n");
            StackTraceElement[] trace = th.getStackTrace();
            for (int i = 0; i < trace.length; i++) {
                StackTraceElement frame = trace[i];
                sb.append("    <frame>\n");
                sb.append("      <class>");
                escape(sb, frame.getClassName());
                sb.append("</class>\n");
                sb.append("      <method>");
                escape(sb, frame.getMethodName());
                sb.append("</method>\n");
                if (frame.getLineNumber() >= 0) {
                    sb.append("      <line>");
                    sb.append(frame.getLineNumber());
                    sb.append("</line>\n");
                }
                sb.append("    </frame>\n");
            }
            sb.append("  </exception>\n");
        }
        sb.append("</record>\n");
        return sb.toString();
    }
    
    public String getHead(Handler h) {
        StringBuffer sb = new StringBuffer();
        String encoding;
        sb.append("<?xml version=\"1.0\"");
        if (h != null) {
            encoding = h.getEncoding();
        } else {
            encoding = null;
        }
        if (encoding == null) {
            encoding = sun.io.Converters.getDefaultEncodingName();
        }
        try {
            Charset cs = Charset.forName(encoding);
            encoding = cs.name();
        } catch (Exception ex) {
        }
        sb.append(" encoding=\"");
        sb.append(encoding);
        sb.append("\"");
        sb.append(" standalone=\"no\"?>\n");
        sb.append("<!DOCTYPE log SYSTEM \"logger.dtd\">\n");
        sb.append("<log>\n");
        return sb.toString();
    }
    
    public String getTail(Handler h) {
        return "</log>\n";
    }
}
