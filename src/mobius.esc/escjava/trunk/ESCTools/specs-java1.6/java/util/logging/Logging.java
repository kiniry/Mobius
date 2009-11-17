package java.util.logging;

import java.util.Enumeration;
import java.util.List;
import java.util.ArrayList;
import sun.management.MXBeanSupport;

class Logging extends MXBeanSupport implements LoggingMXBean {
    private static LogManager logManager = LogManager.getLogManager();
    
    Logging() {
        super(LoggingMXBean.class);
    }
    
    public List getLoggerNames() {
        Enumeration loggers = logManager.getLoggerNames();
        ArrayList array = new ArrayList();
        for (; loggers.hasMoreElements(); ) {
            array.add((String)(String)loggers.nextElement());
        }
        return array;
    }
    private static String EMPTY_STRING = "";
    
    public String getLoggerLevel(String loggerName) {
        Logger l = logManager.getLogger(loggerName);
        if (l == null) {
            return null;
        }
        Level level = l.getLevel();
        if (level == null) {
            return EMPTY_STRING;
        } else {
            return level.getName();
        }
    }
    
    public void setLoggerLevel(String loggerName, String levelName) {
        if (loggerName == null) {
            throw new NullPointerException("loggerName is null");
        }
        Logger logger = logManager.getLogger(loggerName);
        if (logger == null) {
            throw new IllegalArgumentException("Logger " + loggerName + "does not exist");
        }
        Level level = null;
        if (levelName != null) {
            level = Level.parse(levelName);
        }
        logger.setLevel(level);
    }
    
    public String getParentLoggerName(String loggerName) {
        Logger l = logManager.getLogger(loggerName);
        if (l == null) {
            return null;
        }
        Logger p = l.getParent();
        if (p == null) {
            return EMPTY_STRING;
        } else {
            return p.getName();
        }
    }
}
