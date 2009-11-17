package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.util.*;
import sun.awt.AppContext;

class SystemEventQueueUtilities {
    
    /*synthetic*/ static ThreadGroup access$300() {
        return getThreadGroupSafely();
    }
    
    /*synthetic*/ static void access$100(SystemEventQueueUtilities$RunnableEvent x0) {
        processRunnableEvent(x0);
    }
    {
    }
    
    SystemEventQueueUtilities() {
        
    }
    private static final Object classLock = new Object();
    private static final Object rootTableKey = new StringBuffer("SystemEventQueueUtilties.rootTableKey");
    
    private static Map getRootTable() {
        Map rt = (Map)(Map)AppContext.getAppContext().get(rootTableKey);
        if (rt == null) {
            synchronized (rootTableKey) {
                rt = (Map)(Map)AppContext.getAppContext().get(rootTableKey);
                if (rt == null) {
                    rt = Collections.synchronizedMap(new WeakHashMap(4));
                    AppContext.getAppContext().put(rootTableKey, rt);
                }
            }
        }
        return rt;
    }
    {
    }
    {
    }
    
    static void queueComponentWorkRequest(Component root) {
        SystemEventQueueUtilities$ComponentWorkRequest req = (SystemEventQueueUtilities$ComponentWorkRequest)((SystemEventQueueUtilities$ComponentWorkRequest)getRootTable().get(root));
        boolean newWorkRequest = (req == null);
        if (newWorkRequest) {
            req = new SystemEventQueueUtilities$ComponentWorkRequest(root);
        }
        synchronized (req) {
            if (newWorkRequest) {
                getRootTable().put(root, req);
            }
            if (!req.isPending) {
                SwingUtilities.invokeLater(req);
                req.isPending = true;
            }
        }
    }
    
    static void addRunnableCanvas(JRootPane rootPane) {
        synchronized (classLock) {
            if (SystemEventQueueUtilities$SystemEventQueue.get(rootPane) != null) {
                return;
            }
            JLayeredPane layeredPane = rootPane.getLayeredPane();
            if (layeredPane != null) {
                SystemEventQueueUtilities$RunnableCanvas rc = new SystemEventQueueUtilities$RunnableCanvas(rootPane);
                layeredPane.add(rc);
            }
        }
    }
    
    static void removeRunnableCanvas(JRootPane rootPane) {
        synchronized (classLock) {
            Component root = null;
            for (Component c = rootPane; c != null; c = c.getParent()) {
                if ((c instanceof Window) || (c instanceof java.applet.Applet)) {
                    root = c;
                    break;
                }
            }
            if (root != null) {
                getRootTable().remove(root);
            }
            SystemEventQueueUtilities$RunnableCanvas.remove(rootPane);
        }
    }
    
    static Exception postRunnable(Runnable doRun, Object lock) {
        EventQueue systemEventQueue = SystemEventQueueUtilities$SystemEventQueue.get();
        SystemEventQueueUtilities$RunnableEvent event = new SystemEventQueueUtilities$RunnableEvent(doRun, lock);
        if (systemEventQueue != null) {
            systemEventQueue.postEvent(event);
        } else {
            postRunnableCanvasEvent(event);
        }
        return event.exception;
    }
    
    static void restartTimerQueueThread() {
        synchronized (classLock) {
            if (SystemEventQueueUtilities$SystemEventQueue.get() == null) {
                Runnable restarter = new SystemEventQueueUtilities$TimerQueueRestart(null);
                SystemEventQueueUtilities$RunnableEvent event = new SystemEventQueueUtilities$RunnableEvent(restarter, null);
                SystemEventQueueUtilities$RunnableCanvas.postRunnableEventToAll(event);
            }
        }
    }
    {
    }
    {
    }
    
    private static void processRunnableEvent(SystemEventQueueUtilities$RunnableEvent runnableEvent) {
        Object lock = runnableEvent.lock;
        if (lock == null) {
            runnableEvent.doRun.run();
        } else {
            synchronized (lock) {
                try {
                    runnableEvent.doRun.run();
                } catch (Exception e) {
                    runnableEvent.exception = e;
                } finally {
                    if (runnableEvent.lock != null) {
                        runnableEvent.lock.notify();
                    }
                }
            }
        }
    }
    {
    }
    
    private static void postRunnableCanvasEvent(SystemEventQueueUtilities$RunnableEvent e) {
        synchronized (classLock) {
            SystemEventQueueUtilities$RunnableCanvas runnableCanvas = SystemEventQueueUtilities$RunnableCanvas.lookup(e);
            if (runnableCanvas == null) {
                if (e.doRun instanceof SystemEventQueueUtilities$ComponentWorkRequest) {
                    SystemEventQueueUtilities$ComponentWorkRequest req = (SystemEventQueueUtilities$ComponentWorkRequest)(SystemEventQueueUtilities$ComponentWorkRequest)e.doRun;
                    synchronized (req) {
                        req.isPending = false;
                    }
                }
                if (e.doRun instanceof Timer$DoPostEvent) {
                    ((Timer$DoPostEvent)(Timer$DoPostEvent)e.doRun).getTimer().cancelEvent();
                }
                if (e.lock != null) {
                    e.lock.notify();
                }
                return;
            }
            runnableCanvas.addRunnableEvent(e);
            runnableCanvas.repaint();
        }
    }
    
    private static ThreadGroup getThreadGroupSafely() {
        return new Thread().getThreadGroup();
    }
    {
    }
    {
    }
}
