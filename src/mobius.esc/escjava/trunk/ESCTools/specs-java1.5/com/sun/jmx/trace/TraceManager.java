package com.sun.jmx.trace;

import java.io.IOException;
import java.util.logging.Level;
import java.util.logging.Logger;

public class TraceManager implements TraceDestination {
    
    public TraceManager() {
        
    }
    
    private static Level getLevel(int level) {
        switch (level) {
        case TraceTags.LEVEL_DEBUG: 
            return Level.FINEST;
        
        case TraceTags.LEVEL_TRACE: 
            return Level.FINER;
        
        case TraceTags.LEVEL_ERROR: 
            return Level.SEVERE;
        
        default: 
            return null;
        
        }
    }
    
    private static Logger getLogger(int type) {
        switch (type) {
        case TraceTags.INFO_MBEANSERVER: 
            return Logger.getLogger("javax.management.mbeanserver");
        
        case TraceTags.INFO_ADAPTOR_SNMP: 
            return Logger.getLogger("com.sun.jmx.snmp.daemon");
        
        case TraceTags.INFO_SNMP: 
            return Logger.getLogger("com.sun.jmx.snmp");
        
        case TraceTags.INFO_MLET: 
            return Logger.getLogger("javax.management.mlet");
        
        case TraceTags.INFO_MONITOR: 
            return Logger.getLogger("javax.management.monitor");
        
        case TraceTags.INFO_TIMER: 
            return Logger.getLogger("javax.management.timer");
        
        case TraceTags.INFO_MISC: 
            return Logger.getLogger("javax.management.misc");
        
        case TraceTags.INFO_NOTIFICATION: 
            return Logger.getLogger("javax.management.notification");
        
        case TraceTags.INFO_RELATION: 
            return Logger.getLogger("javax.management.relation");
        
        case TraceTags.INFO_MODELMBEAN: 
            return Logger.getLogger("javax.management.modelmbean");
        
        default: 
            return null;
        
        }
    }
    
    public boolean isSelected(int level, int type) {
        Logger logger;
        Level lvl;
        if (((logger = getLogger(type)) != null) && ((lvl = getLevel(level)) != null)) {
            return logger.isLoggable(lvl);
        }
        return false;
    }
    
    public boolean send(int level, int type, String className, String methodName, String info) {
        if (isSelected(level, type)) {
            getLogger(type).logp(getLevel(level), className, methodName, info);
            return true;
        }
        return false;
    }
    
    public boolean send(int level, int type, String className, String methodName, Throwable exception) {
        if (isSelected(level, type)) {
            getLogger(type).log(getLevel(level), className + ": Exception occured in " + methodName, exception);
            return true;
        }
        return false;
    }
    
    public void reset() throws IOException {
    }
    
    void warning(String loggerName, String msg) {
        Logger.getLogger(loggerName).warning(msg);
    }
    
    void fine(String loggerName, String msg) {
        Logger.getLogger(loggerName).fine(msg);
    }
}
