package java.lang;

import java.io.*;

public class Throwable implements Serializable {
    private static final long serialVersionUID = -3042686055658047285L;
    private transient Object backtrace;
    private String detailMessage;
    private Throwable cause = this;
    private StackTraceElement[] stackTrace;
    
    public Throwable() {
        
        fillInStackTrace();
    }
    
    public Throwable(String message) {
        
        fillInStackTrace();
        detailMessage = message;
    }
    
    public Throwable(String message, Throwable cause) {
        
        fillInStackTrace();
        detailMessage = message;
        this.cause = cause;
    }
    
    public Throwable(Throwable cause) {
        
        fillInStackTrace();
        detailMessage = (cause == null ? null : cause.toString());
        this.cause = cause;
    }
    
    public String getMessage() {
        return detailMessage;
    }
    
    public String getLocalizedMessage() {
        return getMessage();
    }
    
    public Throwable getCause() {
        return (cause == this ? null : cause);
    }
    
    public synchronized Throwable initCause(Throwable cause) {
        if (this.cause != this) throw new IllegalStateException("Can\'t overwrite cause");
        if (cause == this) throw new IllegalArgumentException("Self-causation not permitted");
        this.cause = cause;
        return this;
    }
    
    public String toString() {
        String s = getClass().getName();
        String message = getLocalizedMessage();
        return (message != null) ? (s + ": " + message) : s;
    }
    
    public void printStackTrace() {
        printStackTrace(System.err);
    }
    
    public void printStackTrace(PrintStream s) {
        synchronized (s) {
            s.println(this);
            StackTraceElement[] trace = getOurStackTrace();
            for (int i = 0; i < trace.length; i++) s.println("\tat " + trace[i]);
            Throwable ourCause = getCause();
            if (ourCause != null) ourCause.printStackTraceAsCause(s, trace);
        }
    }
    
    private void printStackTraceAsCause(PrintStream s, StackTraceElement[] causedTrace) {
        StackTraceElement[] trace = getOurStackTrace();
        int m = trace.length - 1;
        int n = causedTrace.length - 1;
        while (m >= 0 && n >= 0 && trace[m].equals(causedTrace[n])) {
            m--;
            n--;
        }
        int framesInCommon = trace.length - 1 - m;
        s.println("Caused by: " + this);
        for (int i = 0; i <= m; i++) s.println("\tat " + trace[i]);
        if (framesInCommon != 0) s.println("\t... " + framesInCommon + " more");
        Throwable ourCause = getCause();
        if (ourCause != null) ourCause.printStackTraceAsCause(s, trace);
    }
    
    public void printStackTrace(PrintWriter s) {
        synchronized (s) {
            s.println(this);
            StackTraceElement[] trace = getOurStackTrace();
            for (int i = 0; i < trace.length; i++) s.println("\tat " + trace[i]);
            Throwable ourCause = getCause();
            if (ourCause != null) ourCause.printStackTraceAsCause(s, trace);
        }
    }
    
    private void printStackTraceAsCause(PrintWriter s, StackTraceElement[] causedTrace) {
        StackTraceElement[] trace = getOurStackTrace();
        int m = trace.length - 1;
        int n = causedTrace.length - 1;
        while (m >= 0 && n >= 0 && trace[m].equals(causedTrace[n])) {
            m--;
            n--;
        }
        int framesInCommon = trace.length - 1 - m;
        s.println("Caused by: " + this);
        for (int i = 0; i <= m; i++) s.println("\tat " + trace[i]);
        if (framesInCommon != 0) s.println("\t... " + framesInCommon + " more");
        Throwable ourCause = getCause();
        if (ourCause != null) ourCause.printStackTraceAsCause(s, trace);
    }
    
    public synchronized native Throwable fillInStackTrace();
    
    public StackTraceElement[] getStackTrace() {
        return (StackTraceElement[])(StackTraceElement[])getOurStackTrace().clone();
    }
    
    private synchronized StackTraceElement[] getOurStackTrace() {
        if (stackTrace == null) {
            int depth = getStackTraceDepth();
            stackTrace = new StackTraceElement[depth];
            for (int i = 0; i < depth; i++) stackTrace[i] = getStackTraceElement(i);
        }
        return stackTrace;
    }
    
    public void setStackTrace(StackTraceElement[] stackTrace) {
        StackTraceElement[] defensiveCopy = (StackTraceElement[])(StackTraceElement[])stackTrace.clone();
        for (int i = 0; i < defensiveCopy.length; i++) if (defensiveCopy[i] == null) throw new NullPointerException("stackTrace[" + i + "]");
        this.stackTrace = defensiveCopy;
    }
    
    private native int getStackTraceDepth();
    
    private native StackTraceElement getStackTraceElement(int index);
    
    private synchronized void writeObject(java.io.ObjectOutputStream s) throws IOException {
        getOurStackTrace();
        s.defaultWriteObject();
    }
}
