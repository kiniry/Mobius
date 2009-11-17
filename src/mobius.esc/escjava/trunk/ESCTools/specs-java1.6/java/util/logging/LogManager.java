package java.util.logging;

import java.io.*;
import java.util.*;
import java.security.*;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;

public class LogManager {
    
    /*synthetic*/ static void access$900(LogManager x0) {
        x0.initializeGlobalHandlers();
    }
    
    /*synthetic*/ static Level access$800() {
        return defaultLevel;
    }
    
    /*synthetic*/ static void access$700(Logger x0, Logger x1) {
        doSetParent(x0, x1);
    }
    
    /*synthetic*/ static String[] access$600(LogManager x0, String x1) {
        return x0.parseClassNames(x1);
    }
    
    /*synthetic*/ static boolean access$402(LogManager x0, boolean x1) {
        return x0.initializedGlobalHandlers = x1;
    }
    
    /*synthetic*/ static boolean access$302(LogManager x0, boolean x1) {
        return x0.deathImminent = x1;
    }
    
    /*synthetic*/ static Logger access$102(LogManager x0, Logger x1) {
        return x0.rootLogger = x1;
    }
    
    /*synthetic*/ static Logger access$100(LogManager x0) {
        return x0.rootLogger;
    }
    
    /*synthetic*/ static LogManager access$002(LogManager x0) {
        return manager = x0;
    }
    
    /*synthetic*/ static LogManager access$000() {
        return manager;
    }
    private static LogManager manager;
    private static final Handler[] emptyHandlers = {};
    private Properties props = new Properties();
    private PropertyChangeSupport changes = new PropertyChangeSupport(LogManager.class);
    private static final Level defaultLevel = Level.INFO;
    private Hashtable loggers = new Hashtable();
    private LogManager$LogNode root = new LogManager$LogNode(null);
    private Logger rootLogger;
    private volatile boolean readPrimordialConfiguration;
    private boolean initializedGlobalHandlers = true;
    private boolean deathImminent;
    static {
        AccessController.doPrivileged(new LogManager$1());
    }
    {
    }
    
    protected LogManager() {
        
        try {
            Runtime.getRuntime().addShutdownHook(new LogManager$Cleaner(this, null));
        } catch (IllegalStateException e) {
        }
    }
    
    public static LogManager getLogManager() {
        if (manager != null) {
            manager.readPrimordialConfiguration();
        }
        return manager;
    }
    
    private void readPrimordialConfiguration() {
        if (!readPrimordialConfiguration) {
            synchronized (this) {
                if (!readPrimordialConfiguration) {
                    if (System.out == null) {
                        return;
                    }
                    readPrimordialConfiguration = true;
                    try {
                        AccessController.doPrivileged(new LogManager$2(this));
                    } catch (Exception ex) {
                    }
                }
            }
        }
    }
    
    public void addPropertyChangeListener(PropertyChangeListener l) throws SecurityException {
        if (l == null) {
            throw new NullPointerException();
        }
        checkAccess();
        changes.addPropertyChangeListener(l);
    }
    
    public void removePropertyChangeListener(PropertyChangeListener l) throws SecurityException {
        checkAccess();
        changes.removePropertyChangeListener(l);
    }
    
    synchronized Logger demandLogger(String name) {
        Logger result = getLogger(name);
        if (result == null) {
            result = new Logger(name, null);
            addLogger(result);
            result = getLogger(name);
        }
        return result;
    }
    
    public synchronized boolean addLogger(Logger logger) {
        final String name = logger.getName();
        if (name == null) {
            throw new NullPointerException();
        }
        Logger old = (Logger)loggers.get(name);
        if (old != null) {
            return false;
        }
        loggers.put(name, logger);
        Level level = getLevelProperty(name + ".level", null);
        if (level != null) {
            doSetLevel(logger, level);
        }
        if (getProperty(name + ".handlers") != null) {
            AccessController.doPrivileged(new LogManager$3(this, name));
        }
        int ix = 1;
        for (; ; ) {
            int ix2 = name.indexOf(".", ix);
            if (ix2 < 0) {
                break;
            }
            String pname = name.substring(0, ix2);
            if (getProperty(pname + ".level") != null) {
                Logger plogger = demandLogger(pname);
            }
            if (getProperty(pname + ".handlers") != null) {
                final String nname = pname;
                AccessController.doPrivileged(new LogManager$4(this, nname));
            }
            ix = ix2 + 1;
        }
        LogManager$LogNode node = findNode(name);
        node.logger = logger;
        Logger parent = null;
        LogManager$LogNode nodep = node.parent;
        while (nodep != null) {
            if (nodep.logger != null) {
                parent = nodep.logger;
                break;
            }
            nodep = nodep.parent;
        }
        if (parent != null) {
            doSetParent(logger, parent);
        }
        node.walkAndSetParent(logger);
        return true;
    }
    
    private static void doSetLevel(final Logger logger, final Level level) {
        SecurityManager sm = System.getSecurityManager();
        if (sm == null) {
            logger.setLevel(level);
            return;
        }
        AccessController.doPrivileged(new LogManager$5(logger, level));
    }
    
    private static void doSetParent(final Logger logger, final Logger parent) {
        SecurityManager sm = System.getSecurityManager();
        if (sm == null) {
            logger.setParent(parent);
            return;
        }
        AccessController.doPrivileged(new LogManager$6(logger, parent));
    }
    
    private LogManager$LogNode findNode(String name) {
        if (name == null || name.equals("")) {
            return root;
        }
        LogManager$LogNode node = root;
        while (name.length() > 0) {
            int ix = name.indexOf(".");
            String head;
            if (ix > 0) {
                head = name.substring(0, ix);
                name = name.substring(ix + 1);
            } else {
                head = name;
                name = "";
            }
            if (node.children == null) {
                node.children = new HashMap();
            }
            LogManager$LogNode child = (LogManager$LogNode)(LogManager$LogNode)node.children.get(head);
            if (child == null) {
                child = new LogManager$LogNode(node);
                node.children.put(head, child);
            }
            node = child;
        }
        return node;
    }
    
    public synchronized Logger getLogger(String name) {
        return (Logger)loggers.get(name);
    }
    
    public synchronized Enumeration getLoggerNames() {
        return loggers.keys();
    }
    
    public void readConfiguration() throws IOException, SecurityException {
        checkAccess();
        String cname = System.getProperty("java.util.logging.config.class");
        if (cname != null) {
            try {
                try {
                    Class clz = ClassLoader.getSystemClassLoader().loadClass(cname);
                    clz.newInstance();
                    return;
                } catch (ClassNotFoundException ex) {
                    Class clz = Thread.currentThread().getContextClassLoader().loadClass(cname);
                    clz.newInstance();
                    return;
                }
            } catch (Exception ex) {
                System.err.println("Logging configuration class \"" + cname + "\" failed");
                System.err.println("" + ex);
            }
        }
        String fname = System.getProperty("java.util.logging.config.file");
        if (fname == null) {
            fname = System.getProperty("java.home");
            if (fname == null) {
                throw new Error("Can\'t find java.home ??");
            }
            File f = new File(fname, "lib");
            f = new File(f, "logging.properties");
            fname = f.getCanonicalPath();
        }
        InputStream in = new FileInputStream(fname);
        BufferedInputStream bin = new BufferedInputStream(in);
        try {
            readConfiguration(bin);
        } finally {
            if (in != null) {
                in.close();
            }
        }
    }
    
    public void reset() throws SecurityException {
        checkAccess();
        synchronized (this) {
            props = new Properties();
            initializedGlobalHandlers = true;
        }
        Enumeration enum_ = getLoggerNames();
        while (enum_.hasMoreElements()) {
            String name = (String)(String)enum_.nextElement();
            resetLogger(name);
        }
    }
    
    private void resetLogger(String name) {
        Logger logger = getLogger(name);
        if (logger == null) {
            return;
        }
        Handler[] targets = logger.getHandlers();
        for (int i = 0; i < targets.length; i++) {
            Handler h = targets[i];
            logger.removeHandler(h);
            try {
                h.close();
            } catch (Exception ex) {
            }
        }
        if (name != null && name.equals("")) {
            logger.setLevel(defaultLevel);
        } else {
            logger.setLevel(null);
        }
    }
    
    private String[] parseClassNames(String propertyName) {
        String hands = getProperty(propertyName);
        if (hands == null) {
            return new String[0];
        }
        hands = hands.trim();
        int ix = 0;
        Vector result = new Vector();
        while (ix < hands.length()) {
            int end = ix;
            while (end < hands.length()) {
                if (Character.isWhitespace(hands.charAt(end))) {
                    break;
                }
                if (hands.charAt(end) == ',') {
                    break;
                }
                end++;
            }
            String word = hands.substring(ix, end);
            ix = end + 1;
            word = word.trim();
            if (word.length() == 0) {
                continue;
            }
            result.add(word);
        }
        return (String[])result.toArray(new String[result.size()]);
    }
    
    public void readConfiguration(InputStream ins) throws IOException, SecurityException {
        checkAccess();
        reset();
        props.load(ins);
        String[] names = parseClassNames("config");
        for (int i = 0; i < names.length; i++) {
            String word = names[i];
            try {
                Class clz = ClassLoader.getSystemClassLoader().loadClass(word);
                clz.newInstance();
            } catch (Exception ex) {
                System.err.println("Can\'t load config class \"" + word + "\"");
                System.err.println("" + ex);
            }
        }
        setLevelsOnExistingLoggers();
        changes.firePropertyChange(null, null, null);
        synchronized (this) {
            initializedGlobalHandlers = false;
        }
    }
    
    public String getProperty(String name) {
        return props.getProperty(name);
    }
    
    String getStringProperty(String name, String defaultValue) {
        String val = getProperty(name);
        if (val == null) {
            return defaultValue;
        }
        return val.trim();
    }
    
    int getIntProperty(String name, int defaultValue) {
        String val = getProperty(name);
        if (val == null) {
            return defaultValue;
        }
        try {
            return Integer.parseInt(val.trim());
        } catch (Exception ex) {
            return defaultValue;
        }
    }
    
    boolean getBooleanProperty(String name, boolean defaultValue) {
        String val = getProperty(name);
        if (val == null) {
            return defaultValue;
        }
        val = val.toLowerCase();
        if (val.equals("true") || val.equals("1")) {
            return true;
        } else if (val.equals("false") || val.equals("0")) {
            return false;
        }
        return defaultValue;
    }
    
    Level getLevelProperty(String name, Level defaultValue) {
        String val = getProperty(name);
        if (val == null) {
            return defaultValue;
        }
        try {
            return Level.parse(val.trim());
        } catch (Exception ex) {
            return defaultValue;
        }
    }
    
    Filter getFilterProperty(String name, Filter defaultValue) {
        String val = getProperty(name);
        try {
            if (val != null) {
                Class clz = ClassLoader.getSystemClassLoader().loadClass(val);
                return (Filter)(Filter)clz.newInstance();
            }
        } catch (Exception ex) {
        }
        return defaultValue;
    }
    
    Formatter getFormatterProperty(String name, Formatter defaultValue) {
        String val = getProperty(name);
        try {
            if (val != null) {
                Class clz = ClassLoader.getSystemClassLoader().loadClass(val);
                return (Formatter)(Formatter)clz.newInstance();
            }
        } catch (Exception ex) {
        }
        return defaultValue;
    }
    
    private synchronized void initializeGlobalHandlers() {
        if (initializedGlobalHandlers) {
            return;
        }
        initializedGlobalHandlers = true;
        if (deathImminent) {
            return;
        }
        AccessController.doPrivileged(new LogManager$7(this));
    }
    private Permission ourPermission = new LoggingPermission("control", null);
    
    public void checkAccess() throws SecurityException {
        SecurityManager sm = System.getSecurityManager();
        if (sm == null) {
            return;
        }
        sm.checkPermission(ourPermission);
    }
    {
    }
    {
    }
    
    private synchronized void setLevelsOnExistingLoggers() {
        Enumeration enum_ = props.propertyNames();
        while (enum_.hasMoreElements()) {
            String key = (String)(String)enum_.nextElement();
            if (!key.endsWith(".level")) {
                continue;
            }
            int ix = key.length() - 6;
            String name = key.substring(0, ix);
            Level level = getLevelProperty(key, null);
            if (level == null) {
                System.err.println("Bad level value for property: " + key);
                continue;
            }
            Logger l = getLogger(name);
            if (l == null) {
                continue;
            }
            l.setLevel(level);
        }
    }
    private static LoggingMXBean loggingMXBean = null;
    public static final String LOGGING_MXBEAN_NAME = "java.util.logging:type=Logging";
    
    public static synchronized LoggingMXBean getLoggingMXBean() {
        if (loggingMXBean == null) {
            loggingMXBean = new Logging();
        }
        return loggingMXBean;
    }
}
