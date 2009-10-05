package java.awt;

import java.awt.event.*;
import java.lang.reflect.Array;
import java.util.EventListener;
import java.io.Serializable;
import java.io.ObjectOutputStream;
import java.io.IOException;
import java.util.EventListener;

public class AWTEventMulticaster implements ComponentListener, ContainerListener, FocusListener, KeyListener, MouseListener, MouseMotionListener, WindowListener, WindowFocusListener, WindowStateListener, ActionListener, ItemListener, AdjustmentListener, TextListener, InputMethodListener, HierarchyListener, HierarchyBoundsListener, MouseWheelListener {
    protected final EventListener a;
    protected final EventListener b;
    
    protected AWTEventMulticaster(EventListener a, EventListener b) {
        
        this.a = a;
        this.b = b;
    }
    
    protected EventListener remove(EventListener oldl) {
        if (oldl == a) return b;
        if (oldl == b) return a;
        EventListener a2 = removeInternal(a, oldl);
        EventListener b2 = removeInternal(b, oldl);
        if (a2 == a && b2 == b) {
            return this;
        }
        return addInternal(a2, b2);
    }
    
    public void componentResized(ComponentEvent e) {
        ((ComponentListener)(ComponentListener)a).componentResized(e);
        ((ComponentListener)(ComponentListener)b).componentResized(e);
    }
    
    public void componentMoved(ComponentEvent e) {
        ((ComponentListener)(ComponentListener)a).componentMoved(e);
        ((ComponentListener)(ComponentListener)b).componentMoved(e);
    }
    
    public void componentShown(ComponentEvent e) {
        ((ComponentListener)(ComponentListener)a).componentShown(e);
        ((ComponentListener)(ComponentListener)b).componentShown(e);
    }
    
    public void componentHidden(ComponentEvent e) {
        ((ComponentListener)(ComponentListener)a).componentHidden(e);
        ((ComponentListener)(ComponentListener)b).componentHidden(e);
    }
    
    public void componentAdded(ContainerEvent e) {
        ((ContainerListener)(ContainerListener)a).componentAdded(e);
        ((ContainerListener)(ContainerListener)b).componentAdded(e);
    }
    
    public void componentRemoved(ContainerEvent e) {
        ((ContainerListener)(ContainerListener)a).componentRemoved(e);
        ((ContainerListener)(ContainerListener)b).componentRemoved(e);
    }
    
    public void focusGained(FocusEvent e) {
        ((FocusListener)(FocusListener)a).focusGained(e);
        ((FocusListener)(FocusListener)b).focusGained(e);
    }
    
    public void focusLost(FocusEvent e) {
        ((FocusListener)(FocusListener)a).focusLost(e);
        ((FocusListener)(FocusListener)b).focusLost(e);
    }
    
    public void keyTyped(KeyEvent e) {
        ((KeyListener)(KeyListener)a).keyTyped(e);
        ((KeyListener)(KeyListener)b).keyTyped(e);
    }
    
    public void keyPressed(KeyEvent e) {
        ((KeyListener)(KeyListener)a).keyPressed(e);
        ((KeyListener)(KeyListener)b).keyPressed(e);
    }
    
    public void keyReleased(KeyEvent e) {
        ((KeyListener)(KeyListener)a).keyReleased(e);
        ((KeyListener)(KeyListener)b).keyReleased(e);
    }
    
    public void mouseClicked(MouseEvent e) {
        ((MouseListener)(MouseListener)a).mouseClicked(e);
        ((MouseListener)(MouseListener)b).mouseClicked(e);
    }
    
    public void mousePressed(MouseEvent e) {
        ((MouseListener)(MouseListener)a).mousePressed(e);
        ((MouseListener)(MouseListener)b).mousePressed(e);
    }
    
    public void mouseReleased(MouseEvent e) {
        ((MouseListener)(MouseListener)a).mouseReleased(e);
        ((MouseListener)(MouseListener)b).mouseReleased(e);
    }
    
    public void mouseEntered(MouseEvent e) {
        ((MouseListener)(MouseListener)a).mouseEntered(e);
        ((MouseListener)(MouseListener)b).mouseEntered(e);
    }
    
    public void mouseExited(MouseEvent e) {
        ((MouseListener)(MouseListener)a).mouseExited(e);
        ((MouseListener)(MouseListener)b).mouseExited(e);
    }
    
    public void mouseDragged(MouseEvent e) {
        ((MouseMotionListener)(MouseMotionListener)a).mouseDragged(e);
        ((MouseMotionListener)(MouseMotionListener)b).mouseDragged(e);
    }
    
    public void mouseMoved(MouseEvent e) {
        ((MouseMotionListener)(MouseMotionListener)a).mouseMoved(e);
        ((MouseMotionListener)(MouseMotionListener)b).mouseMoved(e);
    }
    
    public void windowOpened(WindowEvent e) {
        ((WindowListener)(WindowListener)a).windowOpened(e);
        ((WindowListener)(WindowListener)b).windowOpened(e);
    }
    
    public void windowClosing(WindowEvent e) {
        ((WindowListener)(WindowListener)a).windowClosing(e);
        ((WindowListener)(WindowListener)b).windowClosing(e);
    }
    
    public void windowClosed(WindowEvent e) {
        ((WindowListener)(WindowListener)a).windowClosed(e);
        ((WindowListener)(WindowListener)b).windowClosed(e);
    }
    
    public void windowIconified(WindowEvent e) {
        ((WindowListener)(WindowListener)a).windowIconified(e);
        ((WindowListener)(WindowListener)b).windowIconified(e);
    }
    
    public void windowDeiconified(WindowEvent e) {
        ((WindowListener)(WindowListener)a).windowDeiconified(e);
        ((WindowListener)(WindowListener)b).windowDeiconified(e);
    }
    
    public void windowActivated(WindowEvent e) {
        ((WindowListener)(WindowListener)a).windowActivated(e);
        ((WindowListener)(WindowListener)b).windowActivated(e);
    }
    
    public void windowDeactivated(WindowEvent e) {
        ((WindowListener)(WindowListener)a).windowDeactivated(e);
        ((WindowListener)(WindowListener)b).windowDeactivated(e);
    }
    
    public void windowStateChanged(WindowEvent e) {
        ((WindowStateListener)(WindowStateListener)a).windowStateChanged(e);
        ((WindowStateListener)(WindowStateListener)b).windowStateChanged(e);
    }
    
    public void windowGainedFocus(WindowEvent e) {
        ((WindowFocusListener)(WindowFocusListener)a).windowGainedFocus(e);
        ((WindowFocusListener)(WindowFocusListener)b).windowGainedFocus(e);
    }
    
    public void windowLostFocus(WindowEvent e) {
        ((WindowFocusListener)(WindowFocusListener)a).windowLostFocus(e);
        ((WindowFocusListener)(WindowFocusListener)b).windowLostFocus(e);
    }
    
    public void actionPerformed(ActionEvent e) {
        ((ActionListener)(ActionListener)a).actionPerformed(e);
        ((ActionListener)(ActionListener)b).actionPerformed(e);
    }
    
    public void itemStateChanged(ItemEvent e) {
        ((ItemListener)(ItemListener)a).itemStateChanged(e);
        ((ItemListener)(ItemListener)b).itemStateChanged(e);
    }
    
    public void adjustmentValueChanged(AdjustmentEvent e) {
        ((AdjustmentListener)(AdjustmentListener)a).adjustmentValueChanged(e);
        ((AdjustmentListener)(AdjustmentListener)b).adjustmentValueChanged(e);
    }
    
    public void textValueChanged(TextEvent e) {
        ((TextListener)(TextListener)a).textValueChanged(e);
        ((TextListener)(TextListener)b).textValueChanged(e);
    }
    
    public void inputMethodTextChanged(InputMethodEvent e) {
        ((InputMethodListener)(InputMethodListener)a).inputMethodTextChanged(e);
        ((InputMethodListener)(InputMethodListener)b).inputMethodTextChanged(e);
    }
    
    public void caretPositionChanged(InputMethodEvent e) {
        ((InputMethodListener)(InputMethodListener)a).caretPositionChanged(e);
        ((InputMethodListener)(InputMethodListener)b).caretPositionChanged(e);
    }
    
    public void hierarchyChanged(HierarchyEvent e) {
        ((HierarchyListener)(HierarchyListener)a).hierarchyChanged(e);
        ((HierarchyListener)(HierarchyListener)b).hierarchyChanged(e);
    }
    
    public void ancestorMoved(HierarchyEvent e) {
        ((HierarchyBoundsListener)(HierarchyBoundsListener)a).ancestorMoved(e);
        ((HierarchyBoundsListener)(HierarchyBoundsListener)b).ancestorMoved(e);
    }
    
    public void ancestorResized(HierarchyEvent e) {
        ((HierarchyBoundsListener)(HierarchyBoundsListener)a).ancestorResized(e);
        ((HierarchyBoundsListener)(HierarchyBoundsListener)b).ancestorResized(e);
    }
    
    public void mouseWheelMoved(MouseWheelEvent e) {
        ((MouseWheelListener)(MouseWheelListener)a).mouseWheelMoved(e);
        ((MouseWheelListener)(MouseWheelListener)b).mouseWheelMoved(e);
    }
    
    public static ComponentListener add(ComponentListener a, ComponentListener b) {
        return (ComponentListener)(ComponentListener)addInternal(a, b);
    }
    
    public static ContainerListener add(ContainerListener a, ContainerListener b) {
        return (ContainerListener)(ContainerListener)addInternal(a, b);
    }
    
    public static FocusListener add(FocusListener a, FocusListener b) {
        return (FocusListener)(FocusListener)addInternal(a, b);
    }
    
    public static KeyListener add(KeyListener a, KeyListener b) {
        return (KeyListener)(KeyListener)addInternal(a, b);
    }
    
    public static MouseListener add(MouseListener a, MouseListener b) {
        return (MouseListener)(MouseListener)addInternal(a, b);
    }
    
    public static MouseMotionListener add(MouseMotionListener a, MouseMotionListener b) {
        return (MouseMotionListener)(MouseMotionListener)addInternal(a, b);
    }
    
    public static WindowListener add(WindowListener a, WindowListener b) {
        return (WindowListener)(WindowListener)addInternal(a, b);
    }
    
    public static WindowStateListener add(WindowStateListener a, WindowStateListener b) {
        return (WindowStateListener)(WindowStateListener)addInternal(a, b);
    }
    
    public static WindowFocusListener add(WindowFocusListener a, WindowFocusListener b) {
        return (WindowFocusListener)(WindowFocusListener)addInternal(a, b);
    }
    
    public static ActionListener add(ActionListener a, ActionListener b) {
        return (ActionListener)(ActionListener)addInternal(a, b);
    }
    
    public static ItemListener add(ItemListener a, ItemListener b) {
        return (ItemListener)(ItemListener)addInternal(a, b);
    }
    
    public static AdjustmentListener add(AdjustmentListener a, AdjustmentListener b) {
        return (AdjustmentListener)(AdjustmentListener)addInternal(a, b);
    }
    
    public static TextListener add(TextListener a, TextListener b) {
        return (TextListener)(TextListener)addInternal(a, b);
    }
    
    public static InputMethodListener add(InputMethodListener a, InputMethodListener b) {
        return (InputMethodListener)(InputMethodListener)addInternal(a, b);
    }
    
    public static HierarchyListener add(HierarchyListener a, HierarchyListener b) {
        return (HierarchyListener)(HierarchyListener)addInternal(a, b);
    }
    
    public static HierarchyBoundsListener add(HierarchyBoundsListener a, HierarchyBoundsListener b) {
        return (HierarchyBoundsListener)(HierarchyBoundsListener)addInternal(a, b);
    }
    
    public static MouseWheelListener add(MouseWheelListener a, MouseWheelListener b) {
        return (MouseWheelListener)(MouseWheelListener)addInternal(a, b);
    }
    
    public static ComponentListener remove(ComponentListener l, ComponentListener oldl) {
        return (ComponentListener)(ComponentListener)removeInternal(l, oldl);
    }
    
    public static ContainerListener remove(ContainerListener l, ContainerListener oldl) {
        return (ContainerListener)(ContainerListener)removeInternal(l, oldl);
    }
    
    public static FocusListener remove(FocusListener l, FocusListener oldl) {
        return (FocusListener)(FocusListener)removeInternal(l, oldl);
    }
    
    public static KeyListener remove(KeyListener l, KeyListener oldl) {
        return (KeyListener)(KeyListener)removeInternal(l, oldl);
    }
    
    public static MouseListener remove(MouseListener l, MouseListener oldl) {
        return (MouseListener)(MouseListener)removeInternal(l, oldl);
    }
    
    public static MouseMotionListener remove(MouseMotionListener l, MouseMotionListener oldl) {
        return (MouseMotionListener)(MouseMotionListener)removeInternal(l, oldl);
    }
    
    public static WindowListener remove(WindowListener l, WindowListener oldl) {
        return (WindowListener)(WindowListener)removeInternal(l, oldl);
    }
    
    public static WindowStateListener remove(WindowStateListener l, WindowStateListener oldl) {
        return (WindowStateListener)(WindowStateListener)removeInternal(l, oldl);
    }
    
    public static WindowFocusListener remove(WindowFocusListener l, WindowFocusListener oldl) {
        return (WindowFocusListener)(WindowFocusListener)removeInternal(l, oldl);
    }
    
    public static ActionListener remove(ActionListener l, ActionListener oldl) {
        return (ActionListener)(ActionListener)removeInternal(l, oldl);
    }
    
    public static ItemListener remove(ItemListener l, ItemListener oldl) {
        return (ItemListener)(ItemListener)removeInternal(l, oldl);
    }
    
    public static AdjustmentListener remove(AdjustmentListener l, AdjustmentListener oldl) {
        return (AdjustmentListener)(AdjustmentListener)removeInternal(l, oldl);
    }
    
    public static TextListener remove(TextListener l, TextListener oldl) {
        return (TextListener)(TextListener)removeInternal(l, oldl);
    }
    
    public static InputMethodListener remove(InputMethodListener l, InputMethodListener oldl) {
        return (InputMethodListener)(InputMethodListener)removeInternal(l, oldl);
    }
    
    public static HierarchyListener remove(HierarchyListener l, HierarchyListener oldl) {
        return (HierarchyListener)(HierarchyListener)removeInternal(l, oldl);
    }
    
    public static HierarchyBoundsListener remove(HierarchyBoundsListener l, HierarchyBoundsListener oldl) {
        return (HierarchyBoundsListener)(HierarchyBoundsListener)removeInternal(l, oldl);
    }
    
    public static MouseWheelListener remove(MouseWheelListener l, MouseWheelListener oldl) {
        return (MouseWheelListener)(MouseWheelListener)removeInternal(l, oldl);
    }
    
    protected static EventListener addInternal(EventListener a, EventListener b) {
        if (a == null) return b;
        if (b == null) return a;
        return new AWTEventMulticaster(a, b);
    }
    
    protected static EventListener removeInternal(EventListener l, EventListener oldl) {
        if (l == oldl || l == null) {
            return null;
        } else if (l instanceof AWTEventMulticaster) {
            return ((AWTEventMulticaster)(AWTEventMulticaster)l).remove(oldl);
        } else {
            return l;
        }
    }
    
    protected void saveInternal(ObjectOutputStream s, String k) throws IOException {
        if (a instanceof AWTEventMulticaster) {
            ((AWTEventMulticaster)(AWTEventMulticaster)a).saveInternal(s, k);
        } else if (a instanceof Serializable) {
            s.writeObject(k);
            s.writeObject(a);
        }
        if (b instanceof AWTEventMulticaster) {
            ((AWTEventMulticaster)(AWTEventMulticaster)b).saveInternal(s, k);
        } else if (b instanceof Serializable) {
            s.writeObject(k);
            s.writeObject(b);
        }
    }
    
    protected static void save(ObjectOutputStream s, String k, EventListener l) throws IOException {
        if (l == null) {
            return;
        } else if (l instanceof AWTEventMulticaster) {
            ((AWTEventMulticaster)(AWTEventMulticaster)l).saveInternal(s, k);
        } else if (l instanceof Serializable) {
            s.writeObject(k);
            s.writeObject(l);
        }
    }
    
    private static int getListenerCount(EventListener l, Class listenerType) {
        if (l instanceof AWTEventMulticaster) {
            AWTEventMulticaster mc = (AWTEventMulticaster)(AWTEventMulticaster)l;
            return getListenerCount(mc.a, listenerType) + getListenerCount(mc.b, listenerType);
        } else {
            return listenerType.isInstance(l) ? 1 : 0;
        }
    }
    
    private static int populateListenerArray(EventListener[] a, EventListener l, int index) {
        if (l instanceof AWTEventMulticaster) {
            AWTEventMulticaster mc = (AWTEventMulticaster)(AWTEventMulticaster)l;
            int lhs = populateListenerArray(a, mc.a, index);
            return populateListenerArray(a, mc.b, lhs);
        } else if (a.getClass().getComponentType().isInstance(l)) {
            a[index] = l;
            return index + 1;
        } else {
            return index;
        }
    }
    
    public static java.util.EventListener[] getListeners(EventListener l, Class listenerType) {
        int n = getListenerCount(l, listenerType);
        java.util.EventListener[] result = (java.util.EventListener[])(java.util.EventListener[])Array.newInstance(listenerType, n);
        populateListenerArray(result, l, 0);
        return result;
    }
}
