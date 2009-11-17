package java.awt.event;

import java.awt.ActiveEvent;
import java.awt.AWTEvent;

public class InvocationEvent extends AWTEvent implements ActiveEvent {
    public static final int INVOCATION_FIRST = 1200;
    public static final int INVOCATION_DEFAULT = INVOCATION_FIRST;
    public static final int INVOCATION_LAST = INVOCATION_DEFAULT;
    protected Runnable runnable;
    protected Object notifier;
    protected boolean catchExceptions;
    private Exception exception = null;
    private Throwable throwable = null;
    private long when;
    private static final long serialVersionUID = 436056344909459450L;
    
    public InvocationEvent(Object source, Runnable runnable) {
        this(source, runnable, null, false);
    }
    
    public InvocationEvent(Object source, Runnable runnable, Object notifier, boolean catchThrowables) {
        this(source, INVOCATION_DEFAULT, runnable, notifier, catchThrowables);
    }
    
    protected InvocationEvent(Object source, int id, Runnable runnable, Object notifier, boolean catchThrowables) {
        super(source, id);
        this.runnable = runnable;
        this.notifier = notifier;
        this.catchExceptions = catchThrowables;
        this.when = System.currentTimeMillis();
    }
    
    public void dispatch() {
        if (catchExceptions) {
            try {
                runnable.run();
            } catch (Throwable t) {
                if (t instanceof Exception) {
                    exception = (Exception)(Exception)t;
                }
                throwable = t;
            }
        } else {
            runnable.run();
        }
        if (notifier != null) {
            synchronized (notifier) {
                notifier.notifyAll();
            }
        }
    }
    
    public Exception getException() {
        return (catchExceptions) ? exception : null;
    }
    
    public Throwable getThrowable() {
        return (catchExceptions) ? throwable : null;
    }
    
    public long getWhen() {
        return when;
    }
    
    public String paramString() {
        String typeStr;
        switch (id) {
        case INVOCATION_DEFAULT: 
            typeStr = "INVOCATION_DEFAULT";
            break;
        
        default: 
            typeStr = "unknown type";
        
        }
        return typeStr + ",runnable=" + runnable + ",notifier=" + notifier + ",catchExceptions=" + catchExceptions + ",when=" + when;
    }
}
