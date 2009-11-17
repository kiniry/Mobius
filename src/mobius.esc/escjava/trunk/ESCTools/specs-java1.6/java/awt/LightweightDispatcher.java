package java.awt;

import java.awt.event.InputEvent;
import java.awt.event.MouseEvent;
import java.awt.event.MouseWheelEvent;
import java.awt.event.AWTEventListener;
import javax.accessibility.*;
import sun.awt.AppContext;
import sun.awt.DebugHelper;
import sun.awt.SunToolkit;
import sun.awt.dnd.SunDropTargetEvent;

class LightweightDispatcher implements java.io.Serializable, AWTEventListener {
    
    /*synthetic*/ static void access$100(LightweightDispatcher x0, Component x1, MouseEvent x2) {
        x0.trackMouseEnterExit(x1, x2);
    }
    
    /*synthetic*/ static Container access$000(LightweightDispatcher x0) {
        return x0.nativeContainer;
    }
    /*synthetic*/ static final boolean $assertionsDisabled = !LightweightDispatcher.class.desiredAssertionStatus();
    private static final long serialVersionUID = 5184291520170872969L;
    private static final int LWD_MOUSE_DRAGGED_OVER = 1500;
    private static final DebugHelper dbg = DebugHelper.create(LightweightDispatcher.class);
    
    LightweightDispatcher(Container nativeContainer) {
        
        this.nativeContainer = nativeContainer;
        mouseEventTarget = null;
        eventMask = 0;
    }
    
    void dispose() {
        stopListeningForOtherDrags();
        mouseEventTarget = null;
    }
    
    void enableEvents(long events) {
        eventMask |= events;
    }
    
    boolean dispatchEvent(AWTEvent e) {
        boolean ret = false;
        if (e instanceof SunDropTargetEvent) {
            SunDropTargetEvent sdde = (SunDropTargetEvent)(SunDropTargetEvent)e;
            ret = processDropTargetEvent(sdde);
        } else {
            if (e instanceof MouseEvent && (eventMask & MOUSE_MASK) != 0) {
                MouseEvent me = (MouseEvent)(MouseEvent)e;
                ret = processMouseEvent(me);
            }
            if (e.getID() == MouseEvent.MOUSE_MOVED) {
                nativeContainer.updateCursorImmediately();
            }
        }
        return ret;
    }
    
    private boolean isMouseGrab(MouseEvent e) {
        int modifiers = e.getModifiersEx();
        if (e.getID() == MouseEvent.MOUSE_PRESSED || e.getID() == MouseEvent.MOUSE_RELEASED) {
            switch (e.getButton()) {
            case MouseEvent.BUTTON1: 
                modifiers ^= InputEvent.BUTTON1_DOWN_MASK;
                break;
            
            case MouseEvent.BUTTON2: 
                modifiers ^= InputEvent.BUTTON2_DOWN_MASK;
                break;
            
            case MouseEvent.BUTTON3: 
                modifiers ^= InputEvent.BUTTON3_DOWN_MASK;
                break;
            
            }
        }
        return ((modifiers & (InputEvent.BUTTON1_DOWN_MASK | InputEvent.BUTTON2_DOWN_MASK | InputEvent.BUTTON3_DOWN_MASK)) != 0);
    }
    
    private boolean processMouseEvent(MouseEvent e) {
        int id = e.getID();
        Component mouseOver = nativeContainer.getMouseEventTarget(e.getX(), e.getY(), Container.INCLUDE_SELF);
        trackMouseEnterExit(mouseOver, e);
        if (!isMouseGrab(e) && id != MouseEvent.MOUSE_CLICKED) {
            mouseEventTarget = (mouseOver != nativeContainer) ? mouseOver : null;
        }
        if (mouseEventTarget != null) {
            switch (id) {
            case MouseEvent.MOUSE_ENTERED: 
            
            case MouseEvent.MOUSE_EXITED: 
                break;
            
            case MouseEvent.MOUSE_PRESSED: 
                retargetMouseEvent(mouseEventTarget, id, e);
                break;
            
            case MouseEvent.MOUSE_RELEASED: 
                retargetMouseEvent(mouseEventTarget, id, e);
                break;
            
            case MouseEvent.MOUSE_CLICKED: 
                if (mouseOver == mouseEventTarget) {
                    retargetMouseEvent(mouseOver, id, e);
                }
                break;
            
            case MouseEvent.MOUSE_MOVED: 
                retargetMouseEvent(mouseEventTarget, id, e);
                break;
            
            case MouseEvent.MOUSE_DRAGGED: 
                if (isMouseGrab(e)) {
                    retargetMouseEvent(mouseEventTarget, id, e);
                }
                break;
            
            case MouseEvent.MOUSE_WHEEL: 
                if (dbg.on && mouseOver != null) {
                    dbg.println("LD retargeting mouse wheel to " + mouseOver.getName() + ", " + mouseOver.getClass());
                }
                retargetMouseEvent(mouseOver, id, e);
                break;
            
            }
            e.consume();
        }
        return e.isConsumed();
    }
    
    private boolean processDropTargetEvent(SunDropTargetEvent e) {
        int id = e.getID();
        int x = e.getX();
        int y = e.getY();
        if (!nativeContainer.contains(x, y)) {
            final Dimension d = nativeContainer.getSize();
            if (d.width <= x) {
                x = d.width - 1;
            } else if (x < 0) {
                x = 0;
            }
            if (d.height <= y) {
                y = d.height - 1;
            } else if (y < 0) {
                y = 0;
            }
        }
        Component mouseOver = nativeContainer.getDropTargetEventTarget(x, y, Container.INCLUDE_SELF);
        trackMouseEnterExit(mouseOver, e);
        if (mouseOver != nativeContainer && mouseOver != null) {
            switch (id) {
            case SunDropTargetEvent.MOUSE_ENTERED: 
            
            case SunDropTargetEvent.MOUSE_EXITED: 
                break;
            
            default: 
                retargetMouseEvent(mouseOver, id, e);
                e.consume();
                break;
            
            }
        }
        return e.isConsumed();
    }
    
    private void trackMouseEnterExit(Component targetOver, MouseEvent e) {
        Component targetEnter = null;
        int id = e.getID();
        if (e instanceof SunDropTargetEvent && id == MouseEvent.MOUSE_ENTERED && isMouseInNativeContainer == true) {
            targetLastEntered = null;
        } else if (id != MouseEvent.MOUSE_EXITED && id != MouseEvent.MOUSE_DRAGGED && id != LWD_MOUSE_DRAGGED_OVER && isMouseInNativeContainer == false) {
            isMouseInNativeContainer = true;
            startListeningForOtherDrags();
        } else if (id == MouseEvent.MOUSE_EXITED) {
            isMouseInNativeContainer = false;
            stopListeningForOtherDrags();
        }
        if (isMouseInNativeContainer) {
            targetEnter = targetOver;
        }
        if (targetLastEntered == targetEnter) {
            return;
        }
        if (targetLastEntered != null) {
            retargetMouseEvent(targetLastEntered, MouseEvent.MOUSE_EXITED, e);
        }
        if (id == MouseEvent.MOUSE_EXITED) {
            e.consume();
        }
        if (targetEnter != null) {
            retargetMouseEvent(targetEnter, MouseEvent.MOUSE_ENTERED, e);
        }
        if (id == MouseEvent.MOUSE_ENTERED) {
            e.consume();
        }
        targetLastEntered = targetEnter;
    }
    
    private void startListeningForOtherDrags() {
        java.security.AccessController.doPrivileged(new LightweightDispatcher$1(this));
    }
    
    private void stopListeningForOtherDrags() {
        java.security.AccessController.doPrivileged(new LightweightDispatcher$2(this));
    }
    
    public void eventDispatched(AWTEvent e) {
        boolean isForeignDrag = (e instanceof MouseEvent) && !(e instanceof SunDropTargetEvent) && (e.id == MouseEvent.MOUSE_DRAGGED) && (e.getSource() != nativeContainer);
        if (!isForeignDrag) {
            return;
        }
        MouseEvent srcEvent = (MouseEvent)(MouseEvent)e;
        MouseEvent me;
        synchronized (nativeContainer.getTreeLock()) {
            Component srcComponent = srcEvent.getComponent();
            if (!srcComponent.isShowing()) {
                return;
            }
            me = new MouseEvent(nativeContainer, LWD_MOUSE_DRAGGED_OVER, srcEvent.getWhen(), srcEvent.getModifiersEx() | srcEvent.getModifiers(), srcEvent.getX(), srcEvent.getY(), srcEvent.getClickCount(), srcEvent.isPopupTrigger(), srcEvent.getButton());
            ((AWTEvent)srcEvent).copyPrivateDataInto(me);
            final Point ptSrcOrigin = srcComponent.getLocationOnScreen();
            if (AppContext.getAppContext() != nativeContainer.appContext) {
                final MouseEvent mouseEvent = me;
                Runnable r = new LightweightDispatcher$3(this, mouseEvent, ptSrcOrigin);
                SunToolkit.executeOnEventHandlerThread(nativeContainer, r);
                return;
            } else {
                if (!nativeContainer.isShowing()) {
                    return;
                }
                Point ptDstOrigin = nativeContainer.getLocationOnScreen();
                me.translatePoint(ptSrcOrigin.x - ptDstOrigin.x, ptSrcOrigin.y - ptDstOrigin.y);
            }
        }
        Component targetOver = nativeContainer.getMouseEventTarget(me.getX(), me.getY(), Container.INCLUDE_SELF);
        trackMouseEnterExit(targetOver, me);
    }
    
    void retargetMouseEvent(Component target, int id, MouseEvent e) {
        if (target == null) {
            return;
        }
        int x = e.getX();
        int y = e.getY();
        Component component;
        for (component = target; component != null && component != nativeContainer; component = component.getParent()) {
            x -= component.x;
            y -= component.y;
        }
        MouseEvent retargeted;
        if (component != null) {
            if (e instanceof SunDropTargetEvent) {
                retargeted = new SunDropTargetEvent(target, id, x, y, ((SunDropTargetEvent)(SunDropTargetEvent)e).getDispatcher());
            } else if (id == MouseEvent.MOUSE_WHEEL) {
                retargeted = new MouseWheelEvent(target, id, e.getWhen(), e.getModifiersEx() | e.getModifiers(), x, y, e.getClickCount(), e.isPopupTrigger(), ((MouseWheelEvent)(MouseWheelEvent)e).getScrollType(), ((MouseWheelEvent)(MouseWheelEvent)e).getScrollAmount(), ((MouseWheelEvent)(MouseWheelEvent)e).getWheelRotation());
            } else {
                retargeted = new MouseEvent(target, id, e.getWhen(), e.getModifiersEx() | e.getModifiers(), x, y, e.getClickCount(), e.isPopupTrigger(), e.getButton());
            }
            ((AWTEvent)e).copyPrivateDataInto(retargeted);
            if (target == nativeContainer) {
                ((Container)(Container)target).dispatchEventToSelf(retargeted);
            } else {
                if (!$assertionsDisabled && !(AppContext.getAppContext() == target.appContext)) throw new AssertionError();
                if (nativeContainer.modalComp != null) {
                    if (((Container)(Container)nativeContainer.modalComp).isAncestorOf(target)) {
                        target.dispatchEvent(retargeted);
                    } else {
                        e.consume();
                    }
                } else {
                    target.dispatchEvent(retargeted);
                }
            }
        }
    }
    private Container nativeContainer;
    private Component focus;
    private transient Component mouseEventTarget;
    private transient Component targetLastEntered;
    private transient boolean isMouseInNativeContainer = false;
    private Cursor nativeCursor;
    private long eventMask;
    private static final long PROXY_EVENT_MASK = AWTEvent.FOCUS_EVENT_MASK | AWTEvent.KEY_EVENT_MASK | AWTEvent.MOUSE_EVENT_MASK | AWTEvent.MOUSE_MOTION_EVENT_MASK | AWTEvent.MOUSE_WHEEL_EVENT_MASK;
    private static final long MOUSE_MASK = AWTEvent.MOUSE_EVENT_MASK | AWTEvent.MOUSE_MOTION_EVENT_MASK | AWTEvent.MOUSE_WHEEL_EVENT_MASK;
}
