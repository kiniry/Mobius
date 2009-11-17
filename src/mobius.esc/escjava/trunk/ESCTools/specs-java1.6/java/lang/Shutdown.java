package java.lang;

import java.util.HashSet;
import java.util.Iterator;

class Shutdown {
    {
    }
    
    Shutdown() {
        
    }
    {
    }
    private static final int RUNNING = 0;
    private static final int HOOKS = 1;
    private static final int FINALIZERS = 2;
    private static int state = RUNNING;
    private static boolean runFinalizersOnExit = false;
    private static HashSet hooks = null;
    {
    }
    {
    }
    private static Object lock = new Shutdown$Lock(null);
    private static Object haltLock = new Shutdown$Lock(null);
    
    static void setRunFinalizersOnExit(boolean run) {
        synchronized (lock) {
            runFinalizersOnExit = run;
        }
    }
    
    static void add(Thread hook) {
        synchronized (lock) {
            if (state > RUNNING) throw new IllegalStateException("Shutdown in progress");
            if (hook.isAlive()) throw new IllegalArgumentException("Hook already running");
            if (hooks == null) {
                hooks = new HashSet(11);
                hooks.add(new Shutdown$WrappedHook(hook));
                Terminator.setup();
            } else {
                Shutdown$WrappedHook wh = new Shutdown$WrappedHook(hook);
                if (hooks.contains(wh)) throw new IllegalArgumentException("Hook previously registered");
                hooks.add(wh);
            }
        }
    }
    
    static boolean remove(Thread hook) {
        synchronized (lock) {
            if (state > RUNNING) throw new IllegalStateException("Shutdown in progress");
            if (hook == null) throw new NullPointerException();
            if (hooks == null) {
                return false;
            } else {
                boolean rv = hooks.remove(new Shutdown$WrappedHook(hook));
                if (rv && hooks.isEmpty()) {
                    hooks = null;
                    Terminator.teardown();
                }
                return rv;
            }
        }
    }
    
    private static void runHooks() {
        if (hooks == null) return;
        for (Iterator i = hooks.iterator(); i.hasNext(); ) {
            Shutdown.WrappedHook.access$100(((Shutdown$WrappedHook)((Shutdown$WrappedHook)i.next()))).start();
        }
        for (Iterator i = hooks.iterator(); i.hasNext(); ) {
            try {
                Shutdown.WrappedHook.access$100(((Shutdown$WrappedHook)((Shutdown$WrappedHook)i.next()))).join();
            } catch (InterruptedException x) {
                continue;
            }
        }
    }
    
    static void halt(int status) {
        synchronized (haltLock) {
            halt0(status);
        }
    }
    
    static native void halt0(int status);
    
    private static native void runAllFinalizers();
    
    private static void sequence() {
        synchronized (lock) {
            if (state != HOOKS) return;
        }
        runHooks();
        boolean rfoe;
        synchronized (lock) {
            state = FINALIZERS;
            rfoe = runFinalizersOnExit;
        }
        if (rfoe) runAllFinalizers();
    }
    
    static void exit(int status) {
        boolean runMoreFinalizers = false;
        synchronized (lock) {
            if (status != 0) runFinalizersOnExit = false;
            switch (state) {
            case RUNNING: 
                state = HOOKS;
                break;
            
            case HOOKS: 
                break;
            
            case FINALIZERS: 
                if (status != 0) {
                    halt(status);
                } else {
                    runMoreFinalizers = runFinalizersOnExit;
                }
                break;
            
            }
        }
        if (runMoreFinalizers) {
            runAllFinalizers();
            halt(status);
        }
        synchronized (Shutdown.class) {
            sequence();
            halt(status);
        }
    }
    
    static void shutdown() {
        synchronized (lock) {
            switch (state) {
            case RUNNING: 
                state = HOOKS;
                break;
            
            case HOOKS: 
            
            case FINALIZERS: 
                break;
            
            }
        }
        synchronized (Shutdown.class) {
            sequence();
        }
    }
}
