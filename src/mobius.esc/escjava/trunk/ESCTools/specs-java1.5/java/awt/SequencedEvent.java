package java.awt;

import java.awt.AWTEvent;
import java.awt.ActiveEvent;
import java.util.LinkedList;
import sun.awt.AppContext;
import sun.awt.SunToolkit;

class SequencedEvent extends AWTEvent implements ActiveEvent {
    private static final int ID = java.awt.event.FocusEvent.FOCUS_LAST + 1;
    private static final LinkedList list = new LinkedList();
    private final AWTEvent nested;
    private AppContext appContext;
    private boolean disposed;
    
    public SequencedEvent(AWTEvent nested) {
        super(nested.getSource(), ID);
        this.nested = nested;
        synchronized (SequencedEvent.class) {
            list.add(this);
        }
    }
    
    public final void dispatch() {
        try {
            appContext = AppContext.getAppContext();
            if (getFirst() != this) {
                if (EventQueue.isDispatchThread()) {
                    EventDispatchThread edt = (EventDispatchThread)(EventDispatchThread)Thread.currentThread();
                    edt.pumpEvents(SentEvent.ID, new SequencedEvent$1(this));
                } else {
                    while (!isFirstOrDisposed()) {
                        synchronized (SequencedEvent.class) {
                            try {
                                SequencedEvent.class.wait(1000);
                            } catch (InterruptedException e) {
                                break;
                            }
                        }
                    }
                }
            }
            if (!disposed) {
                KeyboardFocusManager.getCurrentKeyboardFocusManager().setCurrentSequencedEvent(this);
                Toolkit.getEventQueue().dispatchEvent(nested);
            }
        } finally {
            dispose();
        }
    }
    
    private static final boolean isOwnerAppContextDisposed(SequencedEvent se) {
        if (se != null) {
            Object target = se.nested.getSource();
            if (target instanceof Component) {
                return ((Component)(Component)target).appContext.isDisposed();
            }
        }
        return false;
    }
    
    public final boolean isFirstOrDisposed() {
        if (disposed) {
            return true;
        }
        return this == getFirstWithContext() || disposed;
    }
    
    private static final synchronized SequencedEvent getFirst() {
        return (SequencedEvent)(SequencedEvent)list.getFirst();
    }
    
    private static final SequencedEvent getFirstWithContext() {
        SequencedEvent first = getFirst();
        while (isOwnerAppContextDisposed(first)) {
            first.dispose();
            first = getFirst();
        }
        return first;
    }
    
    final void dispose() {
        synchronized (SequencedEvent.class) {
            if (disposed) {
                return;
            }
            if (KeyboardFocusManager.getCurrentKeyboardFocusManager().getCurrentSequencedEvent() == this) {
                KeyboardFocusManager.getCurrentKeyboardFocusManager().setCurrentSequencedEvent(null);
            }
            disposed = true;
        }
        if (appContext != null) {
            SunToolkit.postEvent(appContext, new SentEvent());
        }
        SequencedEvent next = null;
        synchronized (SequencedEvent.class) {
            SequencedEvent.class.notifyAll();
            if (list.getFirst() == this) {
                list.removeFirst();
                if (!list.isEmpty()) {
                    next = (SequencedEvent)(SequencedEvent)list.getFirst();
                }
            } else {
                list.remove(this);
            }
        }
        if (next != null && next.appContext != null) {
            SunToolkit.postEvent(next.appContext, new SentEvent());
        }
    }
}
