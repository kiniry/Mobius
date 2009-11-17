package java.awt;

import java.awt.event.FocusEvent;
import java.awt.event.KeyEvent;
import java.awt.event.WindowEvent;
import java.awt.peer.ComponentPeer;
import java.awt.peer.LightweightPeer;
import java.util.LinkedList;
import java.util.Iterator;
import java.util.ListIterator;
import java.util.Set;
import java.util.logging.*;
import sun.awt.AppContext;
import sun.awt.SunToolkit;

public class DefaultKeyboardFocusManager extends KeyboardFocusManager {
    
    /*synthetic*/ static int access$010(DefaultKeyboardFocusManager x0) {
        return x0.inSendMessage--;
    }
    
    /*synthetic*/ static int access$008(DefaultKeyboardFocusManager x0) {
        return x0.inSendMessage++;
    }
    
    public DefaultKeyboardFocusManager() {
        
    }
    private static final Logger focusLog = Logger.getLogger("java.awt.focus.DefaultKeyboardFocusManager");
    private Window realOppositeWindow;
    private Component realOppositeComponent;
    private int inSendMessage;
    private LinkedList enqueuedKeyEvents = new LinkedList();
    private LinkedList typeAheadMarkers = new LinkedList();
    private boolean consumeNextKeyTyped;
    {
    }
    
    private Window getOwningFrameDialog(Window window) {
        while (window != null && !(window instanceof Frame || window instanceof Dialog)) {
            window = (Window)(Window)window.getParent();
        }
        return window;
    }
    
    private void restoreFocus(FocusEvent fe, Window newFocusedWindow) {
        Component realOppositeComponent = this.realOppositeComponent;
        Component vetoedComponent = fe.getComponent();
        if (newFocusedWindow != null && restoreFocus(newFocusedWindow, vetoedComponent, false)) {
        } else if (realOppositeComponent != null && restoreFocus(realOppositeComponent, false)) {
        } else if (fe.getOppositeComponent() != null && restoreFocus(fe.getOppositeComponent(), false)) {
        } else {
            clearGlobalFocusOwner();
        }
    }
    
    private void restoreFocus(WindowEvent we) {
        Window realOppositeWindow = this.realOppositeWindow;
        if (realOppositeWindow != null && restoreFocus(realOppositeWindow, null, false)) {
        } else if (we.getOppositeWindow() != null && restoreFocus(we.getOppositeWindow(), null, false)) {
        } else {
            clearGlobalFocusOwner();
        }
    }
    
    private boolean restoreFocus(Window aWindow, Component vetoedComponent, boolean clearOnFailure) {
        Component toFocus = KeyboardFocusManager.getMostRecentFocusOwner(aWindow);
        if (toFocus != null && toFocus != vetoedComponent && restoreFocus(toFocus, false)) {
            return true;
        } else if (clearOnFailure) {
            clearGlobalFocusOwner();
            return true;
        } else {
            return false;
        }
    }
    
    private boolean restoreFocus(Component toFocus, boolean clearOnFailure) {
        if (toFocus.isShowing() && toFocus.isFocusable() && toFocus.requestFocus(false)) {
            return true;
        } else if (toFocus.nextFocusHelper()) {
            return true;
        } else if (clearOnFailure) {
            clearGlobalFocusOwner();
            return true;
        } else {
            return false;
        }
    }
    {
    }
    
    static boolean sendMessage(Component target, AWTEvent e) {
        e.isPosted = true;
        AppContext myAppContext = AppContext.getAppContext();
        final AppContext targetAppContext = target.appContext;
        final SentEvent se = new DefaultKeyboardFocusManager$DefaultKeyboardFocusManagerSentEvent(e, myAppContext);
        if (myAppContext == targetAppContext) {
            se.dispatch();
        } else {
            if (targetAppContext.isDisposed()) {
                return false;
            }
            SunToolkit.postEvent(targetAppContext, se);
            if (EventQueue.isDispatchThread()) {
                EventDispatchThread edt = (EventDispatchThread)(EventDispatchThread)Thread.currentThread();
                edt.pumpEvents(SentEvent.ID, new DefaultKeyboardFocusManager$1(se, targetAppContext));
            } else {
                synchronized (se) {
                    while (!se.dispatched && !targetAppContext.isDisposed()) {
                        try {
                            se.wait(1000);
                        } catch (InterruptedException ie) {
                            break;
                        }
                    }
                }
            }
        }
        return se.dispatched;
    }
    
    public boolean dispatchEvent(AWTEvent e) {
        if (focusLog.isLoggable(Level.FINE) && (e instanceof WindowEvent || e instanceof FocusEvent)) focusLog.fine("" + e);
        switch (e.getID()) {
        case WindowEvent.WINDOW_GAINED_FOCUS: 
            {
                WindowEvent we = (WindowEvent)(WindowEvent)e;
                Window oldFocusedWindow = getGlobalFocusedWindow();
                Window newFocusedWindow = we.getWindow();
                if (newFocusedWindow == oldFocusedWindow) {
                    break;
                }
                if (oldFocusedWindow != null) {
                    boolean isEventDispatched = sendMessage(oldFocusedWindow, new WindowEvent(oldFocusedWindow, WindowEvent.WINDOW_LOST_FOCUS, newFocusedWindow));
                    if (!isEventDispatched) {
                        setGlobalFocusOwner(null);
                        setGlobalFocusedWindow(null);
                    }
                }
                Window newActiveWindow = getOwningFrameDialog(newFocusedWindow);
                Window currentActiveWindow = getGlobalActiveWindow();
                if (newActiveWindow != currentActiveWindow) {
                    sendMessage(newActiveWindow, new WindowEvent(newActiveWindow, WindowEvent.WINDOW_ACTIVATED, currentActiveWindow));
                    if (newActiveWindow != getGlobalActiveWindow()) {
                        restoreFocus(we);
                        break;
                    }
                }
                setGlobalFocusedWindow(newFocusedWindow);
                if (newFocusedWindow != getGlobalFocusedWindow()) {
                    restoreFocus(we);
                    break;
                }
                setNativeFocusedWindow(newFocusedWindow);
                if (inSendMessage == 0) {
                    Component toFocus = KeyboardFocusManager.getMostRecentFocusOwner(newFocusedWindow);
                    if ((toFocus == null) && newFocusedWindow.isFocusableWindow()) {
                        toFocus = newFocusedWindow.getFocusTraversalPolicy().getInitialComponent(newFocusedWindow);
                    }
                    Component tempLost = null;
                    synchronized (KeyboardFocusManager.class) {
                        tempLost = newFocusedWindow.setTemporaryLostComponent(null);
                    }
                    if (focusLog.isLoggable(Level.FINER)) {
                        focusLog.log(Level.FINER, "tempLost {0}, toFocus {1}", new Object[]{tempLost, toFocus});
                    }
                    setInActivation(true);
                    if (tempLost != null) {
                        tempLost.requestFocusInWindow();
                    }
                    if (toFocus != null && toFocus != tempLost) {
                        toFocus.requestFocusInWindow();
                    }
                    setInActivation(false);
                }
                Window realOppositeWindow = this.realOppositeWindow;
                if (realOppositeWindow != we.getOppositeWindow()) {
                    we = new WindowEvent(newFocusedWindow, WindowEvent.WINDOW_GAINED_FOCUS, realOppositeWindow);
                }
                return typeAheadAssertions(newFocusedWindow, we);
            }
        
        case WindowEvent.WINDOW_ACTIVATED: 
            {
                WindowEvent we = (WindowEvent)(WindowEvent)e;
                Window oldActiveWindow = getGlobalActiveWindow();
                Window newActiveWindow = we.getWindow();
                if (oldActiveWindow == newActiveWindow) {
                    break;
                }
                if (oldActiveWindow != null) {
                    boolean isEventDispatched = sendMessage(oldActiveWindow, new WindowEvent(oldActiveWindow, WindowEvent.WINDOW_DEACTIVATED, newActiveWindow));
                    if (!isEventDispatched) {
                        setGlobalActiveWindow(null);
                    }
                    if (getGlobalActiveWindow() != null) {
                        break;
                    }
                }
                setGlobalActiveWindow(newActiveWindow);
                if (newActiveWindow != getGlobalActiveWindow()) {
                    break;
                }
                return typeAheadAssertions(newActiveWindow, we);
            }
        
        case FocusEvent.FOCUS_GAINED: 
            {
                FocusEvent fe = (FocusEvent)(FocusEvent)e;
                Component oldFocusOwner = getGlobalFocusOwner();
                Component newFocusOwner = fe.getComponent();
                if (oldFocusOwner == newFocusOwner) {
                    if (focusLog.isLoggable(Level.FINE)) focusLog.log(Level.FINE, "Skipping {0} because focus owner is the same", new Object[]{e});
                    dequeueKeyEvents(-1, newFocusOwner);
                    break;
                }
                if (oldFocusOwner != null) {
                    boolean isEventDispatched = sendMessage(oldFocusOwner, new FocusEvent(oldFocusOwner, FocusEvent.FOCUS_LOST, fe.isTemporary(), newFocusOwner));
                    if (!isEventDispatched) {
                        setGlobalFocusOwner(null);
                        if (!fe.isTemporary()) {
                            setGlobalPermanentFocusOwner(null);
                        }
                    }
                }
                Component newFocusedWindow = newFocusOwner;
                while (newFocusedWindow != null && !(newFocusedWindow instanceof Window)) {
                    newFocusedWindow = newFocusedWindow.parent;
                }
                Window currentFocusedWindow = getGlobalFocusedWindow();
                if (newFocusedWindow != null && newFocusedWindow != currentFocusedWindow) {
                    sendMessage(newFocusedWindow, new WindowEvent((Window)(Window)newFocusedWindow, WindowEvent.WINDOW_GAINED_FOCUS, currentFocusedWindow));
                    if (newFocusedWindow != getGlobalFocusedWindow()) {
                        dequeueKeyEvents(-1, newFocusOwner);
                        break;
                    }
                }
                setGlobalFocusOwner(newFocusOwner);
                if (newFocusOwner != getGlobalFocusOwner()) {
                    dequeueKeyEvents(-1, newFocusOwner);
                    if (!disableRestoreFocus) {
                        restoreFocus(fe, (Window)(Window)newFocusedWindow);
                    }
                    break;
                }
                if (!fe.isTemporary()) {
                    setGlobalPermanentFocusOwner(newFocusOwner);
                    if (newFocusOwner != getGlobalPermanentFocusOwner()) {
                        dequeueKeyEvents(-1, newFocusOwner);
                        if (!disableRestoreFocus) {
                            restoreFocus(fe, (Window)(Window)newFocusedWindow);
                        }
                        break;
                    }
                }
                setNativeFocusOwner(getHeavyweight(newFocusOwner));
                Component realOppositeComponent = this.realOppositeComponent;
                if (realOppositeComponent != null && realOppositeComponent != fe.getOppositeComponent()) {
                    fe = new FocusEvent(newFocusOwner, FocusEvent.FOCUS_GAINED, fe.isTemporary(), realOppositeComponent);
                    ((AWTEvent)fe).isPosted = true;
                }
                return typeAheadAssertions(newFocusOwner, fe);
            }
        
        case FocusEvent.FOCUS_LOST: 
            {
                FocusEvent fe = (FocusEvent)(FocusEvent)e;
                Component currentFocusOwner = getGlobalFocusOwner();
                if (currentFocusOwner == null) {
                    if (focusLog.isLoggable(Level.FINE)) focusLog.log(Level.FINE, "Skipping {0} because focus owner is null", new Object[]{e});
                    break;
                }
                if (currentFocusOwner == fe.getOppositeComponent()) {
                    if (focusLog.isLoggable(Level.FINE)) focusLog.log(Level.FINE, "Skipping {0} because current focus owner is equal to opposite", new Object[]{e});
                    break;
                }
                setGlobalFocusOwner(null);
                if (getGlobalFocusOwner() != null) {
                    restoreFocus(currentFocusOwner, true);
                    break;
                }
                if (!fe.isTemporary()) {
                    setGlobalPermanentFocusOwner(null);
                    if (getGlobalPermanentFocusOwner() != null) {
                        restoreFocus(currentFocusOwner, true);
                        break;
                    }
                } else {
                    Window owningWindow = currentFocusOwner.getContainingWindow();
                    if (owningWindow != null) {
                        owningWindow.setTemporaryLostComponent(currentFocusOwner);
                    }
                }
                setNativeFocusOwner(null);
                fe.setSource(currentFocusOwner);
                realOppositeComponent = (fe.getOppositeComponent() != null) ? currentFocusOwner : null;
                return typeAheadAssertions(currentFocusOwner, fe);
            }
        
        case WindowEvent.WINDOW_DEACTIVATED: 
            {
                WindowEvent we = (WindowEvent)(WindowEvent)e;
                Window currentActiveWindow = getGlobalActiveWindow();
                if (currentActiveWindow == null) {
                    break;
                }
                if (currentActiveWindow != e.getSource()) {
                    break;
                }
                setGlobalActiveWindow(null);
                if (getGlobalActiveWindow() != null) {
                    break;
                }
                we.setSource(currentActiveWindow);
                return typeAheadAssertions(currentActiveWindow, we);
            }
        
        case WindowEvent.WINDOW_LOST_FOCUS: 
            {
                WindowEvent we = (WindowEvent)(WindowEvent)e;
                Window currentFocusedWindow = getGlobalFocusedWindow();
                Window losingFocusWindow = we.getWindow();
                Window activeWindow = getGlobalActiveWindow();
                Window oppositeWindow = we.getOppositeWindow();
                if (focusLog.isLoggable(Level.FINE)) focusLog.log(Level.FINE, "Active {0}, Current focused {1}, losing focus {2} opposite {3}", new Object[]{activeWindow, currentFocusedWindow, losingFocusWindow, oppositeWindow});
                if (currentFocusedWindow == null) {
                    break;
                }
                if (inSendMessage == 0 && losingFocusWindow == activeWindow && oppositeWindow == currentFocusedWindow) {
                    break;
                }
                Component currentFocusOwner = getGlobalFocusOwner();
                if (currentFocusOwner != null) {
                    Component oppositeComp = null;
                    if (oppositeWindow != null) {
                        oppositeComp = oppositeWindow.getTemporaryLostComponent();
                        if (oppositeComp == null) {
                            oppositeComp = oppositeWindow.getMostRecentFocusOwner();
                        }
                    }
                    if (oppositeComp == null) {
                        oppositeComp = oppositeWindow;
                    }
                    sendMessage(currentFocusOwner, new FocusEvent(currentFocusOwner, FocusEvent.FOCUS_LOST, true, oppositeComp));
                }
                setGlobalFocusedWindow(null);
                if (getGlobalFocusedWindow() != null) {
                    restoreFocus(currentFocusedWindow, null, true);
                    break;
                }
                setNativeFocusedWindow(null);
                we.setSource(currentFocusedWindow);
                realOppositeWindow = (oppositeWindow != null) ? currentFocusedWindow : null;
                typeAheadAssertions(currentFocusedWindow, we);
                if (oppositeWindow == null) {
                    sendMessage(activeWindow, new WindowEvent(activeWindow, WindowEvent.WINDOW_DEACTIVATED, null));
                    if (getGlobalActiveWindow() != null) {
                        restoreFocus(currentFocusedWindow, null, true);
                    }
                }
                break;
            }
        
        case KeyEvent.KEY_TYPED: 
        
        case KeyEvent.KEY_PRESSED: 
        
        case KeyEvent.KEY_RELEASED: 
            return typeAheadAssertions(null, e);
        
        default: 
            return false;
        
        }
        return true;
    }
    
    public boolean dispatchKeyEvent(KeyEvent e) {
        Component focusOwner = (((AWTEvent)e).isPosted) ? getFocusOwner() : e.getComponent();
        if (focusOwner != null && focusOwner.isShowing() && focusOwner.isFocusable() && focusOwner.isEnabled()) {
            if (!e.isConsumed()) {
                Component comp = e.getComponent();
                if (comp != null && comp.isEnabled()) {
                    redispatchEvent(comp, e);
                }
            }
        }
        boolean stopPostProcessing = false;
        java.util.List processors = getKeyEventPostProcessors();
        if (processors != null) {
            for (java.util.Iterator iter = processors.iterator(); !stopPostProcessing && iter.hasNext(); ) {
                stopPostProcessing = (((KeyEventPostProcessor)((KeyEventPostProcessor)iter.next())).postProcessKeyEvent(e));
            }
        }
        if (!stopPostProcessing) {
            postProcessKeyEvent(e);
        }
        Component source = e.getComponent();
        ComponentPeer peer = source.getPeer();
        if (peer == null || peer instanceof LightweightPeer) {
            Container target = source.getNativeContainer();
            if (target != null) {
                peer = target.getPeer();
            }
        }
        if (peer != null) {
            peer.handleEvent(e);
        }
        return true;
    }
    
    public boolean postProcessKeyEvent(KeyEvent e) {
        if (!e.isConsumed()) {
            Component target = e.getComponent();
            Container p = (Container)(target instanceof Container ? target : target.getParent());
            if (p != null) {
                p.postProcessKeyEvent(e);
            }
        }
        return true;
    }
    
    private void pumpApprovedKeyEvents() {
        KeyEvent ke;
        do {
            ke = null;
            synchronized (this) {
                if (enqueuedKeyEvents.size() != 0) {
                    ke = (KeyEvent)(KeyEvent)enqueuedKeyEvents.getFirst();
                    if (typeAheadMarkers.size() != 0) {
                        DefaultKeyboardFocusManager$TypeAheadMarker marker = (DefaultKeyboardFocusManager$TypeAheadMarker)(DefaultKeyboardFocusManager$TypeAheadMarker)typeAheadMarkers.getFirst();
                        if (ke.getWhen() > marker.after) {
                            ke = null;
                        }
                    }
                    if (ke != null) {
                        focusLog.log(Level.FINER, "Pumping approved event {0}", new Object[]{ke});
                        enqueuedKeyEvents.removeFirst();
                    }
                }
            }
            if (ke != null) {
                preDispatchKeyEvent(ke);
            }
        }         while (ke != null);
    }
    
    void dumpMarkers() {
        if (focusLog.isLoggable(Level.FINEST)) {
            focusLog.log(Level.FINEST, ">>> Markers dump, time: {0}", Long.valueOf(System.currentTimeMillis()));
            synchronized (this) {
                if (typeAheadMarkers.size() != 0) {
                    Iterator iter = typeAheadMarkers.iterator();
                    while (iter.hasNext()) {
                        DefaultKeyboardFocusManager$TypeAheadMarker marker = (DefaultKeyboardFocusManager$TypeAheadMarker)(DefaultKeyboardFocusManager$TypeAheadMarker)iter.next();
                        focusLog.log(Level.FINEST, "    {0}", marker);
                    }
                }
            }
        }
    }
    
    private boolean typeAheadAssertions(Component target, AWTEvent e) {
        pumpApprovedKeyEvents();
        switch (e.getID()) {
        case KeyEvent.KEY_TYPED: 
        
        case KeyEvent.KEY_PRESSED: 
        
        case KeyEvent.KEY_RELEASED: 
            {
                KeyEvent ke = (KeyEvent)(KeyEvent)e;
                synchronized (this) {
                    if (e.isPosted && typeAheadMarkers.size() != 0) {
                        DefaultKeyboardFocusManager$TypeAheadMarker marker = (DefaultKeyboardFocusManager$TypeAheadMarker)(DefaultKeyboardFocusManager$TypeAheadMarker)typeAheadMarkers.getFirst();
                        if (ke.getWhen() > marker.after) {
                            focusLog.log(Level.FINER, "Storing event {0} because of marker {1}", new Object[]{ke, marker});
                            enqueuedKeyEvents.addLast(ke);
                            return true;
                        }
                    }
                }
                return preDispatchKeyEvent(ke);
            }
        
        case FocusEvent.FOCUS_GAINED: 
            focusLog.log(Level.FINEST, "Markers before FOCUS_GAINED on {0}", new Object[]{target});
            dumpMarkers();
            synchronized (this) {
                boolean found = false;
                if (hasMarker(target)) {
                    for (Iterator iter = typeAheadMarkers.iterator(); iter.hasNext(); ) {
                        if (((DefaultKeyboardFocusManager$TypeAheadMarker)(DefaultKeyboardFocusManager$TypeAheadMarker)iter.next()).untilFocused == target) {
                            found = true;
                        } else if (found) {
                            break;
                        }
                        iter.remove();
                    }
                } else {
                    focusLog.log(Level.FINER, "Event without marker {0}", e);
                }
            }
            focusLog.log(Level.FINEST, "Markers after FOCUS_GAINED");
            dumpMarkers();
            redispatchEvent(target, e);
            pumpApprovedKeyEvents();
            return true;
        
        default: 
            redispatchEvent(target, e);
            return true;
        
        }
    }
    
    private boolean hasMarker(Component comp) {
        for (Iterator iter = typeAheadMarkers.iterator(); iter.hasNext(); ) {
            if (((DefaultKeyboardFocusManager$TypeAheadMarker)(DefaultKeyboardFocusManager$TypeAheadMarker)iter.next()).untilFocused == comp) {
                return true;
            }
        }
        return false;
    }
    
    void clearMarkers() {
        synchronized (this) {
            typeAheadMarkers.clear();
        }
    }
    
    private boolean preDispatchKeyEvent(KeyEvent ke) {
        if (((AWTEvent)ke).isPosted) {
            Component focusOwner = getFocusOwner();
            ke.setSource(((focusOwner != null) ? focusOwner : getFocusedWindow()));
        }
        if (ke.getSource() == null) {
            return true;
        }
        EventQueue.setCurrentEventAndMostRecentTime(ke);
        if (KeyboardFocusManager.isProxyActive(ke)) {
            Component source = (Component)(Component)ke.getSource();
            Container target = source.getNativeContainer();
            if (target != null) {
                ComponentPeer peer = target.getPeer();
                if (peer != null) {
                    peer.handleEvent(ke);
                    ke.consume();
                }
            }
            return true;
        }
        java.util.List dispatchers = getKeyEventDispatchers();
        if (dispatchers != null) {
            for (java.util.Iterator iter = dispatchers.iterator(); iter.hasNext(); ) {
                if (((KeyEventDispatcher)((KeyEventDispatcher)iter.next())).dispatchKeyEvent(ke)) {
                    return true;
                }
            }
        }
        return dispatchKeyEvent(ke);
    }
    
    private void consumeTraversalKey(KeyEvent e) {
        e.consume();
        consumeNextKeyTyped = (e.getID() == KeyEvent.KEY_PRESSED) && !e.isActionKey();
    }
    
    private boolean consumeProcessedKeyEvent(KeyEvent e) {
        if ((e.getID() == KeyEvent.KEY_TYPED) && consumeNextKeyTyped) {
            e.consume();
            consumeNextKeyTyped = false;
            return true;
        }
        return false;
    }
    
    public void processKeyEvent(Component focusedComponent, KeyEvent e) {
        if (consumeProcessedKeyEvent(e)) {
            return;
        }
        if (e.getID() == KeyEvent.KEY_TYPED) {
            return;
        }
        if (focusedComponent.getFocusTraversalKeysEnabled() && !e.isConsumed()) {
            AWTKeyStroke stroke = AWTKeyStroke.getAWTKeyStrokeForEvent(e);
            AWTKeyStroke oppStroke = AWTKeyStroke.getAWTKeyStroke(stroke.getKeyCode(), stroke.getModifiers(), !stroke.isOnKeyRelease());
            Set toTest;
            boolean contains;
            boolean containsOpp;
            toTest = focusedComponent.getFocusTraversalKeys(KeyboardFocusManager.FORWARD_TRAVERSAL_KEYS);
            contains = toTest.contains(stroke);
            containsOpp = toTest.contains(oppStroke);
            if (contains || containsOpp) {
                consumeTraversalKey(e);
                if (contains) {
                    focusNextComponent(focusedComponent);
                }
                return;
            } else if (e.getID() == KeyEvent.KEY_PRESSED) {
                consumeNextKeyTyped = false;
            }
            toTest = focusedComponent.getFocusTraversalKeys(KeyboardFocusManager.BACKWARD_TRAVERSAL_KEYS);
            contains = toTest.contains(stroke);
            containsOpp = toTest.contains(oppStroke);
            if (contains || containsOpp) {
                consumeTraversalKey(e);
                if (contains) {
                    focusPreviousComponent(focusedComponent);
                }
                return;
            }
            toTest = focusedComponent.getFocusTraversalKeys(KeyboardFocusManager.UP_CYCLE_TRAVERSAL_KEYS);
            contains = toTest.contains(stroke);
            containsOpp = toTest.contains(oppStroke);
            if (contains || containsOpp) {
                consumeTraversalKey(e);
                if (contains) {
                    upFocusCycle(focusedComponent);
                }
                return;
            }
            if (!((focusedComponent instanceof Container) && ((Container)(Container)focusedComponent).isFocusCycleRoot())) {
                return;
            }
            toTest = focusedComponent.getFocusTraversalKeys(KeyboardFocusManager.DOWN_CYCLE_TRAVERSAL_KEYS);
            contains = toTest.contains(stroke);
            containsOpp = toTest.contains(oppStroke);
            if (contains || containsOpp) {
                consumeTraversalKey(e);
                if (contains) {
                    downFocusCycle((Container)(Container)focusedComponent);
                }
            }
        }
    }
    
    protected synchronized void enqueueKeyEvents(long after, Component untilFocused) {
        if (untilFocused == null) {
            return;
        }
        focusLog.log(Level.FINER, "Enqueue at {0} for {1}", new Object[]{Long.valueOf(after), untilFocused});
        int insertionIndex = 0;
        int i = typeAheadMarkers.size();
        ListIterator iter = typeAheadMarkers.listIterator(i);
        for (; i > 0; i--) {
            DefaultKeyboardFocusManager$TypeAheadMarker marker = (DefaultKeyboardFocusManager$TypeAheadMarker)(DefaultKeyboardFocusManager$TypeAheadMarker)iter.previous();
            if (marker.after <= after) {
                insertionIndex = i;
                break;
            }
        }
        typeAheadMarkers.add(insertionIndex, new DefaultKeyboardFocusManager$TypeAheadMarker(after, untilFocused));
    }
    
    protected synchronized void dequeueKeyEvents(long after, Component untilFocused) {
        if (untilFocused == null) {
            return;
        }
        focusLog.log(Level.FINER, "Dequeue at {0} for {1}", new Object[]{Long.valueOf(after), untilFocused});
        DefaultKeyboardFocusManager$TypeAheadMarker marker;
        ListIterator iter = typeAheadMarkers.listIterator((after >= 0) ? typeAheadMarkers.size() : 0);
        if (after < 0) {
            while (iter.hasNext()) {
                marker = (DefaultKeyboardFocusManager$TypeAheadMarker)(DefaultKeyboardFocusManager$TypeAheadMarker)iter.next();
                if (marker.untilFocused == untilFocused) {
                    iter.remove();
                    return;
                }
            }
        } else {
            while (iter.hasPrevious()) {
                marker = (DefaultKeyboardFocusManager$TypeAheadMarker)(DefaultKeyboardFocusManager$TypeAheadMarker)iter.previous();
                if (marker.untilFocused == untilFocused && marker.after == after) {
                    iter.remove();
                    return;
                }
            }
        }
    }
    
    protected synchronized void discardKeyEvents(Component comp) {
        if (comp == null) {
            return;
        }
        long start = -1;
        for (Iterator iter = typeAheadMarkers.iterator(); iter.hasNext(); ) {
            DefaultKeyboardFocusManager$TypeAheadMarker marker = (DefaultKeyboardFocusManager$TypeAheadMarker)(DefaultKeyboardFocusManager$TypeAheadMarker)iter.next();
            Component toTest = marker.untilFocused;
            boolean match = (toTest == comp);
            while (!match && toTest != null && !(toTest instanceof Window)) {
                toTest = toTest.getParent();
                match = (toTest == comp);
            }
            if (match) {
                if (start < 0) {
                    start = marker.after;
                }
                iter.remove();
            } else if (start >= 0) {
                purgeStampedEvents(start, marker.after);
                start = -1;
            }
        }
        purgeStampedEvents(start, -1);
    }
    
    private void purgeStampedEvents(long start, long end) {
        if (start < 0) {
            return;
        }
        for (Iterator iter = enqueuedKeyEvents.iterator(); iter.hasNext(); ) {
            KeyEvent ke = (KeyEvent)(KeyEvent)iter.next();
            long time = ke.getWhen();
            if (start < time && (end < 0 || time <= end)) {
                iter.remove();
            }
            if (end >= 0 && time > end) {
                break;
            }
        }
    }
    
    public void focusPreviousComponent(Component aComponent) {
        if (aComponent != null) {
            aComponent.transferFocusBackward();
        }
    }
    
    public void focusNextComponent(Component aComponent) {
        if (aComponent != null) {
            aComponent.transferFocus();
        }
    }
    
    public void upFocusCycle(Component aComponent) {
        if (aComponent != null) {
            aComponent.transferFocusUpCycle();
        }
    }
    
    public void downFocusCycle(Container aContainer) {
        if (aContainer != null && aContainer.isFocusCycleRoot()) {
            aContainer.transferFocusDownCycle();
        }
    }
}
