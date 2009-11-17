package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.util.*;

class SystemEventQueueUtilities$RunnableCanvas extends Canvas {
    private static final Graphics nullGraphics = new SystemEventQueueUtilities$RunnableCanvasGraphics(null);
    private static Hashtable runnableCanvasTable = new Hashtable(1);
    private Vector runnableEvents = new Vector(2);
    private boolean isRegistered = false;
    
    SystemEventQueueUtilities$RunnableCanvas(JRootPane rootPane) {
        
        setBounds(0, 0, 1, 1);
        if (runnableCanvasTable.get(Thread.currentThread()) == null) {
            try {
                runnableCanvasTable.put(Thread.currentThread(), this);
                runnableCanvasTable.put(SystemEventQueueUtilities.access$300(), this);
                if (SwingUtilities.isEventDispatchThread()) {
                    isRegistered = true;
                }
            } catch (Exception e) {
                System.err.println("Can\'t register RunnableCanvas");
                e.printStackTrace();
            }
        }
        runnableCanvasTable.put(rootPane, this);
        maybeRegisterEventDispatchThread();
    }
    
    private void maybeRegisterEventDispatchThread() {
        if (!isRegistered) {
            synchronized (this) {
                if (!isRegistered && SwingUtilities.isEventDispatchThread()) {
                    Thread currentThread = Thread.currentThread();
                    if (runnableCanvasTable.get(currentThread) != null) {
                        isRegistered = true;
                    } else {
                        runnableCanvasTable.put(currentThread, this);
                        runnableCanvasTable.put(SystemEventQueueUtilities.access$300(), this);
                        isRegistered = true;
                    }
                }
            }
        }
    }
    
    static SystemEventQueueUtilities$RunnableCanvas lookup(SystemEventQueueUtilities$RunnableEvent e) {
        if (e.doRun instanceof SystemEventQueueUtilities$ComponentWorkRequest) {
            SystemEventQueueUtilities$ComponentWorkRequest req = (SystemEventQueueUtilities$ComponentWorkRequest)(SystemEventQueueUtilities$ComponentWorkRequest)e.doRun;
            synchronized (req) {
                JRootPane rootPane = SwingUtilities.getRootPane(req.component);
                if (rootPane != null) {
                    return (SystemEventQueueUtilities$RunnableCanvas)((SystemEventQueueUtilities$RunnableCanvas)runnableCanvasTable.get(rootPane));
                }
                req.isPending = false;
                return null;
            }
        }
        Object rv = runnableCanvasTable.get(Thread.currentThread());
        if (rv != null) {
            return (SystemEventQueueUtilities$RunnableCanvas)(SystemEventQueueUtilities$RunnableCanvas)rv;
        }
        Object threadGroup;
        try {
            threadGroup = Thread.currentThread().getThreadGroup();
        } catch (SecurityException exc) {
            return null;
        }
        SystemEventQueueUtilities$RunnableCanvas rc = (SystemEventQueueUtilities$RunnableCanvas)(SystemEventQueueUtilities$RunnableCanvas)runnableCanvasTable.get(threadGroup);
        if (rc == null) {
            Enumeration keys = runnableCanvasTable.keys();
            if (keys == null) {
                return null;
            }
            while (keys.hasMoreElements()) {
                Object key = keys.nextElement();
                if ((key instanceof JRootPane) && ((JRootPane)(JRootPane)key).isShowing()) {
                    return (SystemEventQueueUtilities$RunnableCanvas)(SystemEventQueueUtilities$RunnableCanvas)runnableCanvasTable.get(key);
                }
            }
        }
        return rc;
    }
    
    static void postRunnableEventToAll(SystemEventQueueUtilities$RunnableEvent e) {
        SystemEventQueueUtilities$RunnableCanvas currentThreadCanvas;
        ThreadGroup tg;
        try {
            tg = new Thread().getThreadGroup();
        } catch (SecurityException se) {
            tg = null;
        }
        if (tg != null) {
            currentThreadCanvas = (SystemEventQueueUtilities$RunnableCanvas)(SystemEventQueueUtilities$RunnableCanvas)runnableCanvasTable.get(tg);
        } else currentThreadCanvas = null;
        Enumeration keys = runnableCanvasTable.keys();
        while (keys.hasMoreElements()) {
            Object key = keys.nextElement();
            if (key instanceof JRootPane) {
                Object canvas = runnableCanvasTable.get(key);
                if (canvas != currentThreadCanvas) {
                    SystemEventQueueUtilities$RunnableCanvas rc = (SystemEventQueueUtilities$RunnableCanvas)(SystemEventQueueUtilities$RunnableCanvas)canvas;
                    rc.addRunnableEvent(e);
                    rc.repaint();
                }
            }
        }
    }
    
    static void remove(JRootPane rootPane) {
        SystemEventQueueUtilities$RunnableCanvas rc = (SystemEventQueueUtilities$RunnableCanvas)((SystemEventQueueUtilities$RunnableCanvas)runnableCanvasTable.get(rootPane));
        if (rc != null) {
            SystemEventQueueUtilities$RunnableCanvas nextCanvas = null;
            JLayeredPane layeredPane = rootPane.getLayeredPane();
            layeredPane.remove((Component)rc);
            Enumeration keys = runnableCanvasTable.keys();
            while (keys.hasMoreElements()) {
                Object key = keys.nextElement();
                Object next = runnableCanvasTable.get(key);
                if (rc == next) {
                    runnableCanvasTable.remove(key);
                } else if (nextCanvas == null) {
                    nextCanvas = (SystemEventQueueUtilities$RunnableCanvas)(SystemEventQueueUtilities$RunnableCanvas)next;
                }
            }
            SystemEventQueueUtilities$RunnableEvent[] events = rc.getRunnableCanvasEvents();
            int numEvents = (events == null) ? 0 : events.length;
            if (numEvents > 0) {
                if (nextCanvas != null) {
                    for (int counter = 0; counter < numEvents; counter++) {
                        SystemEventQueueUtilities$RunnableEvent e = events[counter];
                        if (e.doRun instanceof Timer$DoPostEvent) nextCanvas.addRunnableEvent(e);
                    }
                    nextCanvas.repaint();
                } else {
                    for (int counter = 0; counter < numEvents; counter++) {
                        SystemEventQueueUtilities$RunnableEvent event = events[counter];
                        if (event.doRun instanceof Timer$DoPostEvent) {
                            ((Timer$DoPostEvent)(Timer$DoPostEvent)event.doRun).getTimer().cancelEvent();
                        }
                    }
                }
            }
        }
    }
    
    public boolean isShowing() {
        return runnableEvents.size() > 0;
    }
    
    public Graphics getGraphics() {
        return nullGraphics;
    }
    
    public Dimension getPreferredSize() {
        return new Dimension(1, 1);
    }
    
    synchronized void addRunnableEvent(SystemEventQueueUtilities$RunnableEvent e) {
        runnableEvents.addElement(e);
    }
    
    private synchronized SystemEventQueueUtilities$RunnableEvent[] getRunnableCanvasEvents() {
        int n = runnableEvents.size();
        if (n == 0) {
            return null;
        } else {
            SystemEventQueueUtilities$RunnableEvent[] rv = new SystemEventQueueUtilities$RunnableEvent[n];
            for (int i = 0; i < n; i++) {
                rv[i] = (SystemEventQueueUtilities$RunnableEvent)((SystemEventQueueUtilities$RunnableEvent)runnableEvents.elementAt(i));
            }
            runnableEvents.removeAllElements();
            return rv;
        }
    }
    
    public void paint(Graphics g) {
        maybeRegisterEventDispatchThread();
    }
    
    public void update(Graphics g) {
        SystemEventQueueUtilities$RunnableEvent[] events = getRunnableCanvasEvents();
        if (events != null) {
            for (int i = 0; i < events.length; i++) {
                SystemEventQueueUtilities.access$100(events[i]);
            }
        }
    }
}
