package java.awt;

import java.awt.event.MouseEvent;
import java.awt.event.ActionEvent;
import java.awt.event.WindowEvent;
import java.lang.reflect.Method;
import java.security.AccessController;
import sun.security.action.GetPropertyAction;
import sun.awt.DebugHelper;
import sun.awt.AWTAutoShutdown;
import sun.awt.SunToolkit;
import sun.awt.dnd.SunDragSourceContextPeer;

class EventDispatchThread extends Thread {
    
    /*synthetic*/ static boolean access$002(EventDispatchThread x0, boolean x1) {
        return x0.doDispatch = x1;
    }
    private static final DebugHelper dbg = DebugHelper.create(EventDispatchThread.class);
    private EventQueue theQueue;
    private boolean doDispatch = true;
    private static final int ANY_EVENT = -1;
    
    EventDispatchThread(ThreadGroup group, String name, EventQueue queue) {
        super(group, name);
        theQueue = queue;
    }
    
    void stopDispatchingImpl(boolean wait) {
        EventDispatchThread$StopDispatchEvent stopEvent = new EventDispatchThread$StopDispatchEvent(this);
        if (Thread.currentThread() != this) {
            theQueue.postEventPrivate(stopEvent);
            if (wait) {
                try {
                    join();
                } catch (InterruptedException e) {
                }
            }
        } else {
            stopEvent.dispatch();
        }
        synchronized (theQueue) {
            if (theQueue.getDispatchThread() == this) {
                theQueue.detachDispatchThread();
            }
        }
    }
    
    public void stopDispatching() {
        stopDispatchingImpl(true);
    }
    
    public void stopDispatchingLater() {
        stopDispatchingImpl(false);
    }
    {
    }
    
    public void run() {
        try {
            pumpEvents(new EventDispatchThread$1(this));
        } finally {
            synchronized (theQueue) {
                if (theQueue.getDispatchThread() == this) {
                    theQueue.detachDispatchThread();
                }
                if (theQueue.peekEvent() != null || !SunToolkit.isPostEventQueueEmpty()) {
                    theQueue.initDispatchThread();
                }
                AWTAutoShutdown.getInstance().notifyThreadFree(this);
            }
        }
    }
    
    void pumpEvents(Conditional cond) {
        pumpEvents(ANY_EVENT, cond);
    }
    
    void pumpEventsForHierarchy(Conditional cond, Component modalComponent) {
        pumpEventsForHierarchy(ANY_EVENT, cond, modalComponent);
    }
    
    void pumpEvents(int id, Conditional cond) {
        pumpEventsForHierarchy(id, cond, null);
    }
    
    void pumpEventsForHierarchy(int id, Conditional cond, Component modalComponent) {
        while (doDispatch && cond.evaluate()) {
            if (isInterrupted() || !pumpOneEventForHierarchy(id, modalComponent)) {
                doDispatch = false;
            }
        }
    }
    
    boolean checkMouseEventForModalJInternalFrame(MouseEvent me, Component modalComp) {
        if (modalComp instanceof javax.swing.JInternalFrame) {
            Container c;
            synchronized (modalComp.getTreeLock()) {
                c = ((Container)(Container)modalComp).getHeavyweightContainer();
            }
            if (me.getSource() == c) return true;
        }
        return false;
    }
    
    boolean pumpOneEventForHierarchy(int id, Component modalComponent) {
        try {
            AWTEvent event;
            boolean eventOK;
            do {
                event = (id == ANY_EVENT) ? theQueue.getNextEvent() : theQueue.getNextEvent(id);
                eventOK = true;
                if (modalComponent != null) {
                    int eventID = event.getID();
                    if (((eventID >= MouseEvent.MOUSE_FIRST && eventID <= MouseEvent.MOUSE_LAST) && !(checkMouseEventForModalJInternalFrame((MouseEvent)(MouseEvent)event, modalComponent))) || (eventID >= ActionEvent.ACTION_FIRST && eventID <= ActionEvent.ACTION_LAST) || eventID == WindowEvent.WINDOW_CLOSING) {
                        Object o = event.getSource();
                        if (o instanceof sun.awt.ModalExclude) {
                        } else if (o instanceof Component) {
                            Component c = (Component)(Component)o;
                            boolean modalExcluded = false;
                            if (modalComponent instanceof Container) {
                                while (c != modalComponent && c != null) {
                                    if ((c instanceof Window) && (sun.awt.SunToolkit.isModalExcluded((Window)(Window)c))) {
                                        modalExcluded = true;
                                        break;
                                    }
                                    c = c.getParent();
                                }
                            }
                            if (!modalExcluded && (c != modalComponent)) {
                                eventOK = false;
                            }
                        }
                    }
                }
                eventOK = eventOK && SunDragSourceContextPeer.checkEvent(event);
                if (!eventOK) {
                    event.consume();
                }
            }             while (eventOK == false);
            if (dbg.on) dbg.println("Dispatching: " + event);
            theQueue.dispatchEvent(event);
            return true;
        } catch (ThreadDeath death) {
            return false;
        } catch (InterruptedException interruptedException) {
            return false;
        } catch (RuntimeException e) {
            processException(e, modalComponent != null);
        } catch (Error e) {
            processException(e, modalComponent != null);
        }
        return true;
    }
    
    private void processException(Throwable e, boolean isModal) {
        if (!handleException(e)) {
            if (isModal) {
                System.err.println("Exception occurred during event dispatching:");
                e.printStackTrace();
            } else if (e instanceof RuntimeException) {
                throw (RuntimeException)(RuntimeException)e;
            } else if (e instanceof Error) {
                throw (Error)(Error)e;
            }
        }
    }
    private static final String handlerPropName = "sun.awt.exception.handler";
    private static String handlerClassName = null;
    private static String NO_HANDLER = new String();
    
    private boolean handleException(Throwable thrown) {
        try {
            if (handlerClassName == NO_HANDLER) {
                return false;
            }
            if (handlerClassName == null) {
                handlerClassName = ((String)(String)AccessController.doPrivileged(new GetPropertyAction(handlerPropName)));
                if (handlerClassName == null) {
                    handlerClassName = NO_HANDLER;
                    return false;
                }
            }
            Method m;
            Object h;
            try {
                ClassLoader cl = Thread.currentThread().getContextClassLoader();
                Class c = Class.forName(handlerClassName, true, cl);
                m = c.getMethod("handle", new Class[]{Throwable.class});
                h = c.newInstance();
            } catch (Throwable x) {
                handlerClassName = NO_HANDLER;
                return false;
            }
            m.invoke(h, new Object[]{thrown});
        } catch (Throwable x) {
            return false;
        }
        return true;
    }
    
    boolean isDispatching(EventQueue eq) {
        return theQueue.equals(eq);
    }
    
    EventQueue getEventQueue() {
        return theQueue;
    }
}
