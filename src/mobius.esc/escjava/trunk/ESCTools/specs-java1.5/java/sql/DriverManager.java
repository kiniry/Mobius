package java.sql;

public class DriverManager {
    static final SQLPermission SET_LOG_PERMISSION = new SQLPermission("setLog");
    
    public static java.io.PrintWriter getLogWriter() {
        synchronized (logSync) {
            return logWriter;
        }
    }
    
    public static void setLogWriter(java.io.PrintWriter out) {
        SecurityManager sec = System.getSecurityManager();
        if (sec != null) {
            sec.checkPermission(SET_LOG_PERMISSION);
        }
        synchronized (logSync) {
            logStream = null;
            logWriter = out;
        }
    }
    
    public static synchronized Connection getConnection(String url, java.util.Properties info) throws SQLException {
        ClassLoader callerCL = DriverManager.getCallerClassLoader();
        return (getConnection(url, info, callerCL));
    }
    
    public static synchronized Connection getConnection(String url, String user, String password) throws SQLException {
        java.util.Properties info = new java.util.Properties();
        ClassLoader callerCL = DriverManager.getCallerClassLoader();
        if (user != null) {
            info.put("user", user);
        }
        if (password != null) {
            info.put("password", password);
        }
        return (getConnection(url, info, callerCL));
    }
    
    public static synchronized Connection getConnection(String url) throws SQLException {
        java.util.Properties info = new java.util.Properties();
        ClassLoader callerCL = DriverManager.getCallerClassLoader();
        return (getConnection(url, info, callerCL));
    }
    
    public static synchronized Driver getDriver(String url) throws SQLException {
        println("DriverManager.getDriver(\"" + url + "\")");
        if (!initialized) {
            initialize();
        }
        ClassLoader callerCL = DriverManager.getCallerClassLoader();
        for (int i = 0; i < drivers.size(); i++) {
            DriverInfo di = (DriverInfo)(DriverInfo)drivers.elementAt(i);
            if (getCallerClass(callerCL, di.driverClassName) != di.driverClass) {
                println("    skipping: " + di);
                continue;
            }
            try {
                println("    trying " + di);
                if (di.driver.acceptsURL(url)) {
                    println("getDriver returning " + di);
                    return (di.driver);
                }
            } catch (SQLException ex) {
            }
        }
        println("getDriver: no suitable driver");
        throw new SQLException("No suitable driver", "08001");
    }
    
    public static synchronized void registerDriver(java.sql.Driver driver) throws SQLException {
        if (!initialized) {
            initialize();
        }
        DriverInfo di = new DriverInfo();
        di.driver = driver;
        di.driverClass = driver.getClass();
        di.driverClassName = di.driverClass.getName();
        drivers.addElement(di);
        println("registerDriver: " + di);
    }
    
    public static synchronized void deregisterDriver(Driver driver) throws SQLException {
        ClassLoader callerCL = DriverManager.getCallerClassLoader();
        println("DriverManager.deregisterDriver: " + driver);
        int i;
        DriverInfo di = null;
        for (i = 0; i < drivers.size(); i++) {
            di = (DriverInfo)(DriverInfo)drivers.elementAt(i);
            if (di.driver == driver) {
                break;
            }
        }
        if (i >= drivers.size()) {
            println("    couldn\'t find driver to unload");
            return;
        }
        if (getCallerClass(callerCL, di.driverClassName) != di.driverClass) {
            throw new SecurityException();
        }
        drivers.removeElementAt(i);
    }
    
    public static synchronized java.util.Enumeration getDrivers() {
        java.util.Vector result = new java.util.Vector();
        if (!initialized) {
            initialize();
        }
        ClassLoader callerCL = DriverManager.getCallerClassLoader();
        for (int i = 0; i < drivers.size(); i++) {
            DriverInfo di = (DriverInfo)(DriverInfo)drivers.elementAt(i);
            if (getCallerClass(callerCL, di.driverClassName) != di.driverClass) {
                println("    skipping: " + di);
                continue;
            }
            result.addElement(di.driver);
        }
        return (result.elements());
    }
    
    public static void setLoginTimeout(int seconds) {
        loginTimeout = seconds;
    }
    
    public static int getLoginTimeout() {
        return (loginTimeout);
    }
    
    
    public static synchronized void setLogStream(java.io.PrintStream out) {
        SecurityManager sec = System.getSecurityManager();
        if (sec != null) {
            sec.checkPermission(SET_LOG_PERMISSION);
        }
        logStream = out;
        if (out != null) logWriter = new java.io.PrintWriter(out); else logWriter = null;
    }
    
    
    public static java.io.PrintStream getLogStream() {
        return logStream;
    }
    
    public static void println(String message) {
        synchronized (logSync) {
            if (logWriter != null) {
                logWriter.println(message);
                logWriter.flush();
            }
        }
    }
    
    private static Class getCallerClass(ClassLoader callerClassLoader, String driverClassName) {
        Class callerC = null;
        try {
            callerC = Class.forName(driverClassName, true, callerClassLoader);
        } catch (Exception ex) {
            callerC = null;
        }
        return callerC;
    }
    
    private static void loadInitialDrivers() {
        String drivers;
        try {
            drivers = (String)(String)java.security.AccessController.doPrivileged(new sun.security.action.GetPropertyAction("jdbc.drivers"));
        } catch (Exception ex) {
            drivers = null;
        }
        println("DriverManager.initialize: jdbc.drivers = " + drivers);
        if (drivers == null) {
            return;
        }
        while (drivers.length() != 0) {
            int x = drivers.indexOf(':');
            String driver;
            if (x < 0) {
                driver = drivers;
                drivers = "";
            } else {
                driver = drivers.substring(0, x);
                drivers = drivers.substring(x + 1);
            }
            if (driver.length() == 0) {
                continue;
            }
            try {
                println("DriverManager.Initialize: loading " + driver);
                Class.forName(driver, true, ClassLoader.getSystemClassLoader());
            } catch (Exception ex) {
                println("DriverManager.Initialize: load failed: " + ex);
            }
        }
    }
    
    private static synchronized Connection getConnection(String url, java.util.Properties info, ClassLoader callerCL) throws SQLException {
        if (callerCL == null) {
            callerCL = Thread.currentThread().getContextClassLoader();
        }
        if (url == null) {
            throw new SQLException("The url cannot be null", "08001");
        }
        println("DriverManager.getConnection(\"" + url + "\")");
        if (!initialized) {
            initialize();
        }
        SQLException reason = null;
        for (int i = 0; i < drivers.size(); i++) {
            DriverInfo di = (DriverInfo)(DriverInfo)drivers.elementAt(i);
            if (getCallerClass(callerCL, di.driverClassName) != di.driverClass) {
                println("    skipping: " + di);
                continue;
            }
            try {
                println("    trying " + di);
                Connection result = di.driver.connect(url, info);
                if (result != null) {
                    println("getConnection returning " + di);
                    return (result);
                }
            } catch (SQLException ex) {
                if (reason == null) {
                    reason = ex;
                }
            }
        }
        if (reason != null) {
            println("getConnection failed: " + reason);
            throw reason;
        }
        println("getConnection: no suitable driver");
        throw new SQLException("No suitable driver", "08001");
    }
    
    static void initialize() {
        if (initialized) {
            return;
        }
        initialized = true;
        loadInitialDrivers();
        println("JDBC DriverManager initialized");
    }
    
    private DriverManager() {
        
    }
    private static java.util.Vector drivers = new java.util.Vector();
    private static int loginTimeout = 0;
    private static java.io.PrintWriter logWriter = null;
    private static java.io.PrintStream logStream = null;
    private static boolean initialized = false;
    private static Object logSync = new Object();
    
    private static native ClassLoader getCallerClassLoader();
}
