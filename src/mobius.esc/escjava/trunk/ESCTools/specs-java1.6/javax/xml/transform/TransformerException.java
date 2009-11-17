package javax.xml.transform;

import java.lang.reflect.Method;
import java.lang.reflect.InvocationTargetException;

public class TransformerException extends Exception {
    SourceLocator locator;
    
    public SourceLocator getLocator() {
        return locator;
    }
    
    public void setLocator(SourceLocator location) {
        locator = location;
    }
    Throwable containedException;
    
    public Throwable getException() {
        return containedException;
    }
    
    public Throwable getCause() {
        return ((containedException == this) ? null : containedException);
    }
    
    public synchronized Throwable initCause(Throwable cause) {
        if (this.containedException != null) {
            throw new IllegalStateException("Can\'t overwrite cause");
        }
        if (cause == this) {
            throw new IllegalArgumentException("Self-causation not permitted");
        }
        this.containedException = cause;
        return this;
    }
    
    public TransformerException(String message) {
        super(message);
        this.containedException = null;
        this.locator = null;
    }
    
    public TransformerException(Throwable e) {
        super(e.toString());
        this.containedException = e;
        this.locator = null;
    }
    
    public TransformerException(String message, Throwable e) {
        super(((message == null) || (message.length() == 0)) ? e.toString() : message);
        this.containedException = e;
        this.locator = null;
    }
    
    public TransformerException(String message, SourceLocator locator) {
        super(message);
        this.containedException = null;
        this.locator = locator;
    }
    
    public TransformerException(String message, SourceLocator locator, Throwable e) {
        super(message);
        this.containedException = e;
        this.locator = locator;
    }
    
    public String getMessageAndLocation() {
        StringBuffer sbuffer = new StringBuffer();
        String message = super.getMessage();
        if (null != message) {
            sbuffer.append(message);
        }
        if (null != locator) {
            String systemID = locator.getSystemId();
            int line = locator.getLineNumber();
            int column = locator.getColumnNumber();
            if (null != systemID) {
                sbuffer.append("; SystemID: ");
                sbuffer.append(systemID);
            }
            if (0 != line) {
                sbuffer.append("; Line#: ");
                sbuffer.append(line);
            }
            if (0 != column) {
                sbuffer.append("; Column#: ");
                sbuffer.append(column);
            }
        }
        return sbuffer.toString();
    }
    
    public String getLocationAsString() {
        if (null != locator) {
            StringBuffer sbuffer = new StringBuffer();
            String systemID = locator.getSystemId();
            int line = locator.getLineNumber();
            int column = locator.getColumnNumber();
            if (null != systemID) {
                sbuffer.append("; SystemID: ");
                sbuffer.append(systemID);
            }
            if (0 != line) {
                sbuffer.append("; Line#: ");
                sbuffer.append(line);
            }
            if (0 != column) {
                sbuffer.append("; Column#: ");
                sbuffer.append(column);
            }
            return sbuffer.toString();
        } else {
            return null;
        }
    }
    
    public void printStackTrace() {
        printStackTrace(new java.io.PrintWriter(System.err, true));
    }
    
    public void printStackTrace(java.io.PrintStream s) {
        printStackTrace(new java.io.PrintWriter(s));
    }
    
    public void printStackTrace(java.io.PrintWriter s) {
        if (s == null) {
            s = new java.io.PrintWriter(System.err, true);
        }
        try {
            String locInfo = getLocationAsString();
            if (null != locInfo) {
                s.println(locInfo);
            }
            super.printStackTrace(s);
        } catch (Throwable e) {
        }
        Throwable exception = getException();
        for (int i = 0; (i < 10) && (null != exception); i++) {
            s.println("---------");
            try {
                if (exception instanceof TransformerException) {
                    String locInfo = ((TransformerException)(TransformerException)exception).getLocationAsString();
                    if (null != locInfo) {
                        s.println(locInfo);
                    }
                }
                exception.printStackTrace(s);
            } catch (Throwable e) {
                s.println("Could not print stack trace...");
            }
            try {
                Method meth = ((Object)exception).getClass().getMethod("getException", null);
                if (null != meth) {
                    Throwable prev = exception;
                    exception = (Throwable)(Throwable)meth.invoke(exception, null);
                    if (prev == exception) {
                        break;
                    }
                } else {
                    exception = null;
                }
            } catch (InvocationTargetException ite) {
                exception = null;
            } catch (IllegalAccessException iae) {
                exception = null;
            } catch (NoSuchMethodException nsme) {
                exception = null;
            }
        }
        s.flush();
    }
}
