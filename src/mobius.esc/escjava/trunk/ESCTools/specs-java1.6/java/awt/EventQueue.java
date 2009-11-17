package java.awt;

import java.awt.event.ActionEvent;
import java.awt.event.FocusEvent;
import java.awt.event.InputEvent;
import java.awt.event.InputMethodEvent;
import java.awt.event.InvocationEvent;
import java.awt.event.KeyEvent;
import java.awt.event.MouseEvent;
import java.awt.event.PaintEvent;
import java.awt.event.WindowEvent;
import java.awt.ActiveEvent;
import java.awt.peer.ComponentPeer;
import java.awt.peer.LightweightPeer;
import java.util.EmptyStackException;
import java.lang.ref.WeakReference;
import java.lang.reflect.InvocationTargetException;
import java.security.AccessController;
import sun.awt.PeerEvent;
import sun.awt.SunToolkit;
import sun.awt.DebugHelper;
import sun.awt.AWTAutoShutdown;
import sun.awt.AppContext;

public class EventQueue {
    
    /*synthetic*/ static ClassLoader access$200(EventQueue x0) {
        return x0.classLoader;
    }
    
    /*synthetic*/ static String access$100(EventQueue x0) {
        return x0.name;
    }
    
    /*synthetic*/ static ThreadGroup access$000(EventQueue x0) {
        return x0.threadGroup;
    }
    private static final DebugHelper dbg = DebugHelper.create(EventQueue.class);
    private static int threadInitNumber;
    
    private static synchronized int nextThreadNum() {
        return threadInitNumber++;
    }
    private static final int LOW_PRIORITY = 0;
    private static final int NORM_PRIORITY = 1;
    private static final int HIGH_PRIORITY = 2;
    private static final int ULTIMATE_PRIORITY = 3;
    private static final int NUM_PRIORITIES = ULTIMATE_PRIORITY + 1;
    private Queue[] queues = new Queue[NUM_PRIORITIES];
    private EventQueue nextQueue;
    private EventQueue previousQueue;
    private EventDispatchThread dispatchThread;
    private final ThreadGroup threadGroup = Thread.currentThread().getThreadGroup();
    private final ClassLoader classLoader = Thread.currentThread().getContextClassLoader();
    private static final boolean debug = false;
    private long mostRecentEventTime = System.currentTimeMillis();
    private WeakReference currentEvent;
    private int waitForID;
    private final String name = "AWT-EventQueue-" + nextThreadNum();
    
    public EventQueue() {
        
        for (int i = 0; i < NUM_PRIORITIES; i++) {
            queues[i] = new Queue();
        }
    }
    
    public void postEvent(AWTEvent theEvent) {
        SunToolkit.flushPendingEvents();
        postEventPrivate(theEvent);
    }
    
    final void postEventPrivate(AWTEvent theEvent) {
        theEvent.isPosted = true;
        synchronized (this) {
            int id = theEvent.getID();
            if (nextQueue != null) {
                nextQueue.postEventPrivate(theEvent);
            } else if (theEvent instanceof PeerEvent && (((PeerEvent)(PeerEvent)theEvent).getFlags() & PeerEvent.ULTIMATE_PRIORITY_EVENT) != 0) {
                postEvent(theEvent, ULTIMATE_PRIORITY);
            } else if (theEvent instanceof PeerEvent && (((PeerEvent)(PeerEvent)theEvent).getFlags() & PeerEvent.PRIORITY_EVENT) != 0) {
                postEvent(theEvent, HIGH_PRIORITY);
            } else if (id == PaintEvent.PAINT || id == PaintEvent.UPDATE) {
                postEvent(theEvent, LOW_PRIORITY);
            } else {
                postEvent(theEvent, NORM_PRIORITY);
            }
        }
    }
    
    private void postEvent(AWTEvent theEvent, int priority) {
        if (dispatchThread == null) {
            if (theEvent.getSource() == AWTAutoShutdown.getInstance()) {
                return;
            } else {
                initDispatchThread();
            }
        }
        Object source = theEvent.getSource();
        if (source instanceof Component) {
            ComponentPeer sourcePeer = ((Component)(Component)source).peer;
            if (sourcePeer != null && theEvent instanceof PaintEvent && !(sourcePeer instanceof LightweightPeer)) {
                sourcePeer.coalescePaintEvent((PaintEvent)(PaintEvent)theEvent);
            }
        }
        EventQueueItem newItem = new EventQueueItem(theEvent);
        boolean notifyID = (theEvent.getID() == this.waitForID);
        if (queues[priority].head == null) {
            boolean shouldNotify = noEvents();
            queues[priority].head = queues[priority].tail = newItem;
            if (shouldNotify) {
                if (theEvent.getSource() != AWTAutoShutdown.getInstance()) {
                    AWTAutoShutdown.getInstance().notifyThreadBusy(dispatchThread);
                }
                notifyAll();
            } else if (notifyID) {
                notifyAll();
            }
        } else {
            boolean isPeerEvent = theEvent instanceof PeerEvent;
            if (source instanceof Component) {
                EventQueueItem q = queues[priority].head;
                if (theEvent.id == Event.MOUSE_MOVE || theEvent.id == Event.MOUSE_DRAG) {
                    EventQueueItem qm;
                    for (qm = q; qm != null; qm = qm.next) {
                        if ((qm.event instanceof MouseEvent) && qm.id != theEvent.id) {
                            q = qm;
                        }
                    }
                }
                for (; q != null; q = q.next) {
                    if (q.event.getSource() == source && q.id == newItem.id) {
                        AWTEvent coalescedEvent = ((Component)(Component)source).coalesceEvents(q.event, theEvent);
                        if (isPeerEvent && coalescedEvent == null && q.event instanceof PeerEvent) {
                            coalescedEvent = ((PeerEvent)(PeerEvent)q.event).coalesceEvents((PeerEvent)(PeerEvent)theEvent);
                        }
                        if (coalescedEvent != null) {
                            q.event = coalescedEvent;
                            return;
                        }
                    }
                }
            }
            queues[priority].tail.next = newItem;
            queues[priority].tail = newItem;
            if (notifyID) {
                notifyAll();
            }
        }
    }
    
    private boolean noEvents() {
        for (int i = 0; i < NUM_PRIORITIES; i++) {
            if (queues[i].head != null) {
                return false;
            }
        }
        return true;
    }
    
    public AWTEvent getNextEvent() throws InterruptedException {
        do {
            SunToolkit.flushPendingEvents();
            synchronized (this) {
                for (int i = NUM_PRIORITIES - 1; i >= 0; i--) {
                    if (queues[i].head != null) {
                        EventQueueItem eqi = queues[i].head;
                        queues[i].head = eqi.next;
                        if (eqi.next == null) {
                            queues[i].tail = null;
                        }
                        return eqi.event;
                    }
                }
                AWTAutoShutdown.getInstance().notifyThreadFree(dispatchThread);
                wait();
            }
        }         while (true);
    }
    
    AWTEvent getNextEvent(int id) throws InterruptedException {
        do {
            SunToolkit.flushPendingEvents();
            synchronized (this) {
                for (int i = 0; i < NUM_PRIORITIES; i++) {
                    for (EventQueueItem entry = queues[i].head, prev = null; entry != null; prev = entry, entry = entry.next) {
                        if (entry.id == id) {
                            if (prev == null) {
                                queues[i].head = entry.next;
                            } else {
                                prev.next = entry.next;
                            }
                            if (queues[i].tail == entry) {
                                queues[i].tail = prev;
                            }
                            return entry.event;
                        }
                    }
                }
                this.waitForID = id;
                wait();
                this.waitForID = 0;
            }
        }         while (true);
    }
    
    public synchronized AWTEvent peekEvent() {
        for (int i = NUM_PRIORITIES - 1; i >= 0; i--) {
            if (queues[i].head != null) {
                return queues[i].head.event;
            }
        }
        return null;
    }
    
    public synchronized AWTEvent peekEvent(int id) {
        for (int i = NUM_PRIORITIES - 1; i >= 0; i--) {
            EventQueueItem q = queues[i].head;
            for (; q != null; q = q.next) {
                if (q.id == id) {
                    return q.event;
                }
            }
        }
        return null;
    }
    
    protected void dispatchEvent(AWTEvent event) {
        event.isPosted = true;
        Object src = event.getSource();
        if (event instanceof ActiveEvent) {
            setCurrentEventAndMostRecentTimeImpl(event);
            ((ActiveEvent)(ActiveEvent)event).dispatch();
        } else if (src instanceof Component) {
            ((Component)(Component)src).dispatchEvent(event);
            event.dispatched();
        } else if (src instanceof MenuComponent) {
            ((MenuComponent)(MenuComponent)src).dispatchEvent(event);
        } else if (src instanceof AWTAutoShutdown) {
            if (noEvents()) {
                dispatchThread.stopDispatching();
            }
        } else {
            System.err.println("unable to dispatch event: " + event);
        }
    }
    
    public static long getMostRecentEventTime() {
        return Toolkit.getEventQueue().getMostRecentEventTimeImpl();
    }
    
    private synchronized long getMostRecentEventTimeImpl() {
        return (Thread.currentThread() == dispatchThread) ? mostRecentEventTime : System.currentTimeMillis();
    }
    
    synchronized long getMostRecentEventTimeEx() {
        return mostRecentEventTime;
    }
    
    public static AWTEvent getCurrentEvent() {
        return Toolkit.getEventQueue().getCurrentEventImpl();
    }
    
    private synchronized AWTEvent getCurrentEventImpl() {
        return (Thread.currentThread() == dispatchThread) ? ((AWTEvent)(AWTEvent)currentEvent.get()) : null;
    }
    
    public synchronized void push(EventQueue newEventQueue) {
        ;
        if (nextQueue != null) {
            nextQueue.push(newEventQueue);
            return;
        }
        synchronized (newEventQueue) {
            while (peekEvent() != null) {
                try {
                    newEventQueue.postEventPrivate(getNextEvent());
                } catch (InterruptedException ie) {
                    ;
                }
            }
            newEventQueue.previousQueue = this;
        }
        if (dispatchThread != null) {
            dispatchThread.stopDispatchingLater();
        }
        nextQueue = newEventQueue;
        AppContext appContext = AppContext.getAppContext();
        if (appContext.get(AppContext.EVENT_QUEUE_KEY) == this) {
            appContext.put(AppContext.EVENT_QUEUE_KEY, newEventQueue);
        }
    }
    
    protected void pop() throws EmptyStackException {
        ;
        EventQueue prev = previousQueue;
        synchronized ((prev != null) ? prev : this) {
            synchronized (this) {
                if (nextQueue != null) {
                    nextQueue.pop();
                    return;
                }
                if (previousQueue == null) {
                    throw new EmptyStackException();
                }
                previousQueue.nextQueue = null;
                while (peekEvent() != null) {
                    try {
                        previousQueue.postEventPrivate(getNextEvent());
                    } catch (InterruptedException ie) {
                        ;
                    }
                }
                AppContext appContext = AppContext.getAppContext();
                if (appContext.get(AppContext.EVENT_QUEUE_KEY) == this) {
                    appContext.put(AppContext.EVENT_QUEUE_KEY, previousQueue);
                }
                previousQueue = null;
            }
        }
        EventDispatchThread dt = this.dispatchThread;
        if (dt != null) {
            dt.stopDispatching();
        }
    }
    
    public static boolean isDispatchThread() {
        EventQueue eq = Toolkit.getEventQueue();
        EventQueue next = eq.nextQueue;
        while (next != null) {
            eq = next;
            next = eq.nextQueue;
        }
        return (Thread.currentThread() == eq.dispatchThread);
    }
    
    final void initDispatchThread() {
        synchronized (this) {
            if (dispatchThread == null && !threadGroup.isDestroyed()) {
                dispatchThread = (EventDispatchThread)(EventDispatchThread)AccessController.doPrivileged(new EventQueue$1(this));
                AWTAutoShutdown.getInstance().notifyThreadBusy(dispatchThread);
                dispatchThread.start();
            }
        }
    }
    
    final void detachDispatchThread() {
        dispatchThread = null;
    }
    
    final EventDispatchThread getDispatchThread() {
        return dispatchThread;
    }
    
    final void removeSourceEvents(Object source, boolean removeAllEvents) {
        SunToolkit.flushPendingEvents();
        synchronized (this) {
            for (int i = 0; i < NUM_PRIORITIES; i++) {
                EventQueueItem entry = queues[i].head;
                EventQueueItem prev = null;
                while (entry != null) {
                    if ((entry.event.getSource() == source) && (removeAllEvents || !(entry.event instanceof SequencedEvent || entry.event instanceof SentEvent || entry.event instanceof FocusEvent || entry.event instanceof WindowEvent || entry.event instanceof KeyEvent || entry.event instanceof InputMethodEvent))) {
                        if (entry.event instanceof SequencedEvent) {
                            ((SequencedEvent)(SequencedEvent)entry.event).dispose();
                        }
                        if (entry.event instanceof SentEvent) {
                            ((SentEvent)(SentEvent)entry.event).dispose();
                        }
                        if (prev == null) {
                            queues[i].head = entry.next;
                        } else {
                            prev.next = entry.next;
                        }
                    } else {
                        prev = entry;
                    }
                    entry = entry.next;
                }
                queues[i].tail = prev;
            }
        }
    }
    
    static void setCurrentEventAndMostRecentTime(AWTEvent e) {
        Toolkit.getEventQueue().setCurrentEventAndMostRecentTimeImpl(e);
    }
    
    private synchronized void setCurrentEventAndMostRecentTimeImpl(AWTEvent e) {
        if (Thread.currentThread() != dispatchThread) {
            return;
        }
        currentEvent = new WeakReference(e);
        long mostRecentEventTime2 = Long.MIN_VALUE;
        if (e instanceof InputEvent) {
            InputEvent ie = (InputEvent)(InputEvent)e;
            mostRecentEventTime2 = ie.getWhen();
        } else if (e instanceof InputMethodEvent) {
            InputMethodEvent ime = (InputMethodEvent)(InputMethodEvent)e;
            mostRecentEventTime2 = ime.getWhen();
        } else if (e instanceof ActionEvent) {
            ActionEvent ae = (ActionEvent)(ActionEvent)e;
            mostRecentEventTime2 = ae.getWhen();
        } else if (e instanceof InvocationEvent) {
            InvocationEvent ie = (InvocationEvent)(InvocationEvent)e;
            mostRecentEventTime2 = ie.getWhen();
        }
        mostRecentEventTime = Math.max(mostRecentEventTime, mostRecentEventTime2);
    }
    
    public static void invokeLater(Runnable runnable) {
        Toolkit.getEventQueue().postEvent(new InvocationEvent(Toolkit.getDefaultToolkit(), runnable));
    }
    
    public static void invokeAndWait(Runnable runnable) throws InterruptedException, InvocationTargetException {
        if (EventQueue.isDispatchThread()) {
            throw new Error("Cannot call invokeAndWait from the event dispatcher thread");
        }
        {
        }
        Object lock = new EventQueue$1AWTInvocationLock();
        InvocationEvent event = new InvocationEvent(Toolkit.getDefaultToolkit(), runnable, lock, true);
        synchronized (lock) {
            Toolkit.getEventQueue().postEvent(event);
            lock.wait();
        }
        Throwable eventThrowable = event.getThrowable();
        if (eventThrowable != null) {
            throw new InvocationTargetException(eventThrowable);
        }
    }
    
    private void wakeup(boolean isShutdown) {
        synchronized (this) {
            if (nextQueue != null) {
                nextQueue.wakeup(isShutdown);
            } else if (dispatchThread != null) {
                notifyAll();
            } else if (!isShutdown) {
                initDispatchThread();
            }
        }
    }
}
