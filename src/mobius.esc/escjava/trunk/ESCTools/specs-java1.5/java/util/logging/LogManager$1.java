package java.util.logging;

import java.io.*;
import java.util.*;
import java.security.*;

class LogManager$1 implements PrivilegedAction {
    
    LogManager$1() {
        
    }
    
    public Object run() {
        String cname = null;
        try {
            cname = System.getProperty("java.util.logging.manager");
            if (cname != null) {
                try {
                    Class clz = ClassLoader.getSystemClassLoader().loadClass(cname);
                    LogManager.access$002((LogManager)(LogManager)clz.newInstance());
                } catch (ClassNotFoundException ex) {
                    Class clz = Thread.currentThread().getContextClassLoader().loadClass(cname);
                    LogManager.access$002((LogManager)(LogManager)clz.newInstance());
                }
            }
        } catch (Exception ex) {
            System.err.println("Could not load Logmanager \"" + cname + "\"");
            ex.printStackTrace();
        }
        if (LogManager.access$000() == null) {
            LogManager.access$002(new LogManager());
        }
        LogManager.access$102(LogManager.access$000(), new LogManager$RootLogger(LogManager.access$000(), null));
        LogManager.access$000().addLogger(LogManager.access$100(LogManager.access$000()));
        Logger.global.setLogManager(LogManager.access$000());
        LogManager.access$000().addLogger(Logger.global);
        return null;
    }
}
