package java.util.logging;

import java.util.*;
import java.io.*;

public class LogRecord implements java.io.Serializable {
    private static long globalSequenceNumber;
    private static int nextThreadId = 10;
    private static ThreadLocal threadIds = new ThreadLocal();
    private Level level;
    private long sequenceNumber;
    private String sourceClassName;
    private String sourceMethodName;
    private String message;
    private int threadID;
    private long millis;
    private Throwable thrown;
    private String loggerName;
    private String resourceBundleName;
    private transient boolean needToInferCaller;
    private transient Object[] parameters;
    private transient ResourceBundle resourceBundle;
    
    public LogRecord(Level level, String msg) {
        
        level.getClass();
        this.level = level;
        message = msg;
        synchronized (LogRecord.class) {
            sequenceNumber = globalSequenceNumber++;
            Integer id = (Integer)(Integer)threadIds.get();
            if (id == null) {
                id = new Integer(nextThreadId++);
                threadIds.set(id);
            }
            threadID = id.intValue();
        }
        millis = System.currentTimeMillis();
        needToInferCaller = true;
    }
    
    public String getLoggerName() {
        return loggerName;
    }
    
    public void setLoggerName(String name) {
        loggerName = name;
    }
    
    public ResourceBundle getResourceBundle() {
        return resourceBundle;
    }
    
    public void setResourceBundle(ResourceBundle bundle) {
        resourceBundle = bundle;
    }
    
    public String getResourceBundleName() {
        return resourceBundleName;
    }
    
    public void setResourceBundleName(String name) {
        resourceBundleName = name;
    }
    
    public Level getLevel() {
        return level;
    }
    
    public void setLevel(Level level) {
        if (level == null) {
            throw new NullPointerException();
        }
        this.level = level;
    }
    
    public long getSequenceNumber() {
        return sequenceNumber;
    }
    
    public void setSequenceNumber(long seq) {
        sequenceNumber = seq;
    }
    
    public String getSourceClassName() {
        if (needToInferCaller) {
            inferCaller();
        }
        return sourceClassName;
    }
    
    public void setSourceClassName(String sourceClassName) {
        this.sourceClassName = sourceClassName;
        needToInferCaller = false;
    }
    
    public String getSourceMethodName() {
        if (needToInferCaller) {
            inferCaller();
        }
        return sourceMethodName;
    }
    
    public void setSourceMethodName(String sourceMethodName) {
        this.sourceMethodName = sourceMethodName;
        needToInferCaller = false;
    }
    
    public String getMessage() {
        return message;
    }
    
    public void setMessage(String message) {
        this.message = message;
    }
    
    public Object[] getParameters() {
        return parameters;
    }
    
    public void setParameters(Object[] parameters) {
        this.parameters = parameters;
    }
    
    public int getThreadID() {
        return threadID;
    }
    
    public void setThreadID(int threadID) {
        this.threadID = threadID;
    }
    
    public long getMillis() {
        return millis;
    }
    
    public void setMillis(long millis) {
        this.millis = millis;
    }
    
    public Throwable getThrown() {
        return thrown;
    }
    
    public void setThrown(Throwable thrown) {
        this.thrown = thrown;
    }
    private static final long serialVersionUID = 5372048053134512534L;
    
    private void writeObject(ObjectOutputStream out) throws IOException {
        out.defaultWriteObject();
        out.writeByte(1);
        out.writeByte(0);
        if (parameters == null) {
            out.writeInt(-1);
            return;
        }
        out.writeInt(parameters.length);
        for (int i = 0; i < parameters.length; i++) {
            if (parameters[i] == null) {
                out.writeObject(null);
            } else {
                out.writeObject(parameters[i].toString());
            }
        }
    }
    
    private void readObject(ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        byte major = in.readByte();
        byte minor = in.readByte();
        if (major != 1) {
            throw new IOException("LogRecord: bad version: " + major + "." + minor);
        }
        int len = in.readInt();
        if (len == -1) {
            parameters = null;
        } else {
            parameters = new Object[len];
            for (int i = 0; i < parameters.length; i++) {
                parameters[i] = in.readObject();
            }
        }
        if (resourceBundleName != null) {
            try {
                resourceBundle = ResourceBundle.getBundle(resourceBundleName);
            } catch (MissingResourceException ex) {
                resourceBundle = null;
            }
        }
        needToInferCaller = false;
    }
    
    private void inferCaller() {
        needToInferCaller = false;
        StackTraceElement[] stack = (new Throwable()).getStackTrace();
        int ix = 0;
        while (ix < stack.length) {
            StackTraceElement frame = stack[ix];
            String cname = frame.getClassName();
            if (cname.equals("java.util.logging.Logger")) {
                break;
            }
            ix++;
        }
        while (ix < stack.length) {
            StackTraceElement frame = stack[ix];
            String cname = frame.getClassName();
            if (!cname.equals("java.util.logging.Logger")) {
                setSourceClassName(cname);
                setSourceMethodName(frame.getMethodName());
                return;
            }
            ix++;
        }
    }
}
