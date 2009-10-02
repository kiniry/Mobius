package java.lang;

import java.security.AccessController;
import java.security.AccessControlContext;
import java.util.Map;
import java.util.HashMap;
import sun.misc.SoftCache;
import sun.nio.ch.Interruptible;
import sun.security.util.SecurityConstants;

public class Thread implements Runnable {
    
    private static native void registerNatives();
    static {
        registerNatives();
    }
    private char[] name;
    private int priority;
    private Thread threadQ;
    private long eetop;
    private boolean started;
    private boolean single_step;
    private boolean daemon = false;
    private boolean stillborn = false;
    private Runnable target;
    private ThreadGroup group;
    private ClassLoader contextClassLoader;
    private AccessControlContext inheritedAccessControlContext;
    private static int threadInitNumber;
    
    private static synchronized int nextThreadNum() {
        return threadInitNumber++;
    }
    ThreadLocal$ThreadLocalMap threadLocals = null;
    ThreadLocal$ThreadLocalMap inheritableThreadLocals = null;
    private long stackSize;
    private long tid;
    private static long threadSeqNumber;
    private int threadStatus = 0;
    
    private static synchronized long nextThreadID() {
        return ++threadSeqNumber;
    }
    private volatile Interruptible blocker;
    private Object blockerLock = new Object();
    
    void blockedOn(Interruptible b) {
        synchronized (blockerLock) {
            blocker = b;
        }
    }
    public static final int MIN_PRIORITY = 1;
    public static final int NORM_PRIORITY = 5;
    public static final int MAX_PRIORITY = 10;
    
    public static native Thread currentThread();
    
    public static native void yield();
    
    public static native void sleep(long millis) throws InterruptedException;
    
    public static void sleep(long millis, int nanos) throws InterruptedException {
        if (millis < 0) {
            throw new IllegalArgumentException("timeout value is negative");
        }
        if (nanos < 0 || nanos > 999999) {
            throw new IllegalArgumentException("nanosecond timeout value out of range");
        }
        if (nanos >= 500000 || (nanos != 0 && millis == 0)) {
            millis++;
        }
        sleep(millis);
    }
    
    private void init(ThreadGroup g, Runnable target, String name, long stackSize) {
        Thread parent = currentThread();
        SecurityManager security = System.getSecurityManager();
        if (g == null) {
            if (security != null) {
                g = security.getThreadGroup();
            }
            if (g == null) {
                g = parent.getThreadGroup();
            }
        }
        g.checkAccess();
        if (security != null) {
            if (isCCLOverridden(getClass())) {
                security.checkPermission(SUBCLASS_IMPLEMENTATION_PERMISSION);
            }
        }
        g.addUnstarted();
        this.group = g;
        this.daemon = parent.isDaemon();
        this.priority = parent.getPriority();
        this.name = name.toCharArray();
        if (security == null || isCCLOverridden(parent.getClass())) this.contextClassLoader = parent.getContextClassLoader(); else this.contextClassLoader = parent.contextClassLoader;
        this.inheritedAccessControlContext = AccessController.getContext();
        this.target = target;
        setPriority(priority);
        if (parent.inheritableThreadLocals != null) this.inheritableThreadLocals = ThreadLocal.createInheritedMap(parent.inheritableThreadLocals);
        this.stackSize = stackSize;
        tid = nextThreadID();
    }
    
    public Thread() {
        
        init(null, null, "Thread-" + nextThreadNum(), 0);
    }
    
    public Thread(Runnable target) {
        
        init(null, target, "Thread-" + nextThreadNum(), 0);
    }
    
    public Thread(ThreadGroup group, Runnable target) {
        
        init(group, target, "Thread-" + nextThreadNum(), 0);
    }
    
    public Thread(String name) {
        
        init(null, null, name, 0);
    }
    
    public Thread(ThreadGroup group, String name) {
        
        init(group, null, name, 0);
    }
    
    public Thread(Runnable target, String name) {
        
        init(null, target, name, 0);
    }
    
    public Thread(ThreadGroup group, Runnable target, String name) {
        
        init(group, target, name, 0);
    }
    
    public Thread(ThreadGroup group, Runnable target, String name, long stackSize) {
        
        init(group, target, name, stackSize);
    }
    
    public synchronized void start() {
        if (started) throw new IllegalThreadStateException();
        started = true;
        group.add(this);
        start0();
    }
    
    private native void start0();
    
    public void run() {
        if (target != null) {
            target.run();
        }
    }
    
    private void exit() {
        if (group != null) {
            group.remove(this);
            group = null;
        }
        target = null;
        threadLocals = null;
        inheritableThreadLocals = null;
        inheritedAccessControlContext = null;
        blocker = null;
        uncaughtExceptionHandler = null;
    }
    
    
    public final void stop() {
        synchronized (this) {
            if (!this.isAlive()) return;
            SecurityManager security = System.getSecurityManager();
            if (security != null) {
                checkAccess();
                if (this != Thread.currentThread()) {
                    security.checkPermission(SecurityConstants.STOP_THREAD_PERMISSION);
                }
            }
            resume();
            stop0(new ThreadDeath());
        }
    }
    
    
    public final synchronized void stop(Throwable obj) {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            checkAccess();
            if ((this != Thread.currentThread()) || (!(obj instanceof ThreadDeath))) {
                security.checkPermission(SecurityConstants.STOP_THREAD_PERMISSION);
            }
        }
        resume();
        stop0(obj);
    }
    
    public void interrupt() {
        if (this != Thread.currentThread()) checkAccess();
        synchronized (blockerLock) {
            Interruptible b = blocker;
            if (b != null) {
                interrupt0();
                b.interrupt();
                return;
            }
        }
        interrupt0();
    }
    
    public static boolean interrupted() {
        return currentThread().isInterrupted(true);
    }
    
    public boolean isInterrupted() {
        return isInterrupted(false);
    }
    
    private native boolean isInterrupted(boolean ClearInterrupted);
    
    
    public void destroy() {
        throw new NoSuchMethodError();
    }
    
    public final native boolean isAlive();
    
    
    public final void suspend() {
        checkAccess();
        suspend0();
    }
    
    
    public final void resume() {
        checkAccess();
        resume0();
    }
    
    public final void setPriority(int newPriority) {
        checkAccess();
        if (newPriority > MAX_PRIORITY || newPriority < MIN_PRIORITY) {
            throw new IllegalArgumentException();
        }
        if (newPriority > group.getMaxPriority()) {
            newPriority = group.getMaxPriority();
        }
        setPriority0(priority = newPriority);
    }
    
    public final int getPriority() {
        return priority;
    }
    
    public final void setName(String name) {
        checkAccess();
        this.name = name.toCharArray();
    }
    
    public final String getName() {
        return String.valueOf(name);
    }
    
    public final ThreadGroup getThreadGroup() {
        return group;
    }
    
    public static int activeCount() {
        return currentThread().getThreadGroup().activeCount();
    }
    
    public static int enumerate(Thread[] tarray) {
        return currentThread().getThreadGroup().enumerate(tarray);
    }
    
    
    public native int countStackFrames();
    
    public final synchronized void join(long millis) throws InterruptedException {
        long base = System.currentTimeMillis();
        long now = 0;
        if (millis < 0) {
            throw new IllegalArgumentException("timeout value is negative");
        }
        if (millis == 0) {
            while (isAlive()) {
                wait(0);
            }
        } else {
            while (isAlive()) {
                long delay = millis - now;
                if (delay <= 0) {
                    break;
                }
                wait(delay);
                now = System.currentTimeMillis() - base;
            }
        }
    }
    
    public final synchronized void join(long millis, int nanos) throws InterruptedException {
        if (millis < 0) {
            throw new IllegalArgumentException("timeout value is negative");
        }
        if (nanos < 0 || nanos > 999999) {
            throw new IllegalArgumentException("nanosecond timeout value out of range");
        }
        if (nanos >= 500000 || (nanos != 0 && millis == 0)) {
            millis++;
        }
        join(millis);
    }
    
    public final void join() throws InterruptedException {
        join(0);
    }
    
    public static void dumpStack() {
        new Exception("Stack trace").printStackTrace();
    }
    
    public final void setDaemon(boolean on) {
        checkAccess();
        if (isAlive()) {
            throw new IllegalThreadStateException();
        }
        daemon = on;
    }
    
    public final boolean isDaemon() {
        return daemon;
    }
    
    public final void checkAccess() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkAccess(this);
        }
    }
    
    public String toString() {
        ThreadGroup group = getThreadGroup();
        if (group != null) {
            return "Thread[" + getName() + "," + getPriority() + "," + group.getName() + "]";
        } else {
            return "Thread[" + getName() + "," + getPriority() + "," + "" + "]";
        }
    }
    
    public ClassLoader getContextClassLoader() {
        if (contextClassLoader == null) return null;
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            ClassLoader ccl = ClassLoader.getCallerClassLoader();
            if (ccl != null && ccl != contextClassLoader && !contextClassLoader.isAncestor(ccl)) {
                sm.checkPermission(SecurityConstants.GET_CLASSLOADER_PERMISSION);
            }
        }
        return contextClassLoader;
    }
    
    public void setContextClassLoader(ClassLoader cl) {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(new RuntimePermission("setContextClassLoader"));
        }
        contextClassLoader = cl;
    }
    
    public static native boolean holdsLock(Object obj);
    private static final StackTraceElement[] EMPTY_STACK_TRACE = new StackTraceElement[0];
    
    public StackTraceElement[] getStackTrace() {
        if (this != Thread.currentThread()) {
            SecurityManager security = System.getSecurityManager();
            if (security != null) {
                security.checkPermission(SecurityConstants.GET_STACK_TRACE_PERMISSION);
            }
            if (!isAlive()) {
                return EMPTY_STACK_TRACE;
            }
            StackTraceElement[][] stackTraceArray = dumpThreads(new Thread[]{this});
            StackTraceElement[] stackTrace = stackTraceArray[0];
            if (stackTrace == null) {
                stackTrace = EMPTY_STACK_TRACE;
            }
            return stackTrace;
        } else {
            return (new Exception()).getStackTrace();
        }
    }
    
    public static Map getAllStackTraces() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkPermission(SecurityConstants.GET_STACK_TRACE_PERMISSION);
            security.checkPermission(SecurityConstants.MODIFY_THREADGROUP_PERMISSION);
        }
        Thread[] threads = getThreads();
        StackTraceElement[][] traces = dumpThreads(threads);
        Map m = new HashMap(threads.length);
        for (int i = 0; i < threads.length; i++) {
            StackTraceElement[] stackTrace = traces[i];
            if (stackTrace != null) {
                m.put(threads[i], stackTrace);
            }
        }
        return m;
    }
    private static final RuntimePermission SUBCLASS_IMPLEMENTATION_PERMISSION = new RuntimePermission("enableContextClassLoaderOverride");
    private static final SoftCache subclassAudits = new SoftCache(10);
    
    private static boolean isCCLOverridden(Class cl) {
        if (cl == Thread.class) return false;
        Boolean result = null;
        synchronized (subclassAudits) {
            result = (Boolean)(Boolean)subclassAudits.get(cl);
            if (result == null) {
                result = new Boolean(auditSubclass(cl));
                subclassAudits.put(cl, result);
            }
        }
        return result.booleanValue();
    }
    
    private static boolean auditSubclass(final Class subcl) {
        Boolean result = (Boolean)(Boolean)AccessController.doPrivileged(new Thread$1(subcl));
        return result.booleanValue();
    }
    
    private static native StackTraceElement[][] dumpThreads(Thread[] threads);
    
    private static native Thread[] getThreads();
    
    public long getId() {
        return tid;
    }
    {
    }
    
    public Thread$State getState() {
        return sun.misc.VM.toThreadState(threadStatus);
    }
    {
    }
    private volatile Thread$UncaughtExceptionHandler uncaughtExceptionHandler;
    private static volatile Thread$UncaughtExceptionHandler defaultUncaughtExceptionHandler;
    
    public static void setDefaultUncaughtExceptionHandler(Thread$UncaughtExceptionHandler eh) {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(new RuntimePermission("setDefaultUncaughtExceptionHandler"));
        }
        defaultUncaughtExceptionHandler = eh;
    }
    
    public static Thread$UncaughtExceptionHandler getDefaultUncaughtExceptionHandler() {
        return defaultUncaughtExceptionHandler;
    }
    
    public Thread$UncaughtExceptionHandler getUncaughtExceptionHandler() {
        return uncaughtExceptionHandler != null ? uncaughtExceptionHandler : group;
    }
    
    public void setUncaughtExceptionHandler(Thread$UncaughtExceptionHandler eh) {
        checkAccess();
        uncaughtExceptionHandler = eh;
    }
    
    private void dispatchUncaughtException(Throwable e) {
        getUncaughtExceptionHandler().uncaughtException(this, e);
    }
    
    private native void setPriority0(int newPriority);
    
    private native void stop0(Object o);
    
    private native void suspend0();
    
    private native void resume0();
    
    private native void interrupt0();
}
