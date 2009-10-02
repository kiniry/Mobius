package javax.swing.plaf.basic;

import java.awt.event.*;
import java.awt.dnd.DragSource;
import javax.swing.*;
import sun.awt.dnd.SunDragSourceContextPeer;
import sun.awt.AppContext;

class DragRecognitionSupport {
    
    DragRecognitionSupport() {
        
    }
    private int motionThreshold;
    private MouseEvent dndArmedEvent;
    private JComponent component;
    {
    }
    
    private static DragRecognitionSupport getDragRecognitionSupport() {
        DragRecognitionSupport support = (DragRecognitionSupport)(DragRecognitionSupport)AppContext.getAppContext().get(DragRecognitionSupport.class);
        if (support == null) {
            support = new DragRecognitionSupport();
            AppContext.getAppContext().put(DragRecognitionSupport.class, support);
        }
        return support;
    }
    
    public static boolean mousePressed(MouseEvent me) {
        return ((DragRecognitionSupport)getDragRecognitionSupport()).mousePressedImpl(me);
    }
    
    public static MouseEvent mouseReleased(MouseEvent me) {
        return ((DragRecognitionSupport)getDragRecognitionSupport()).mouseReleasedImpl(me);
    }
    
    public static boolean mouseDragged(MouseEvent me, DragRecognitionSupport$BeforeDrag bd) {
        return ((DragRecognitionSupport)getDragRecognitionSupport()).mouseDraggedImpl(me, bd);
    }
    
    private void clearState() {
        dndArmedEvent = null;
        component = null;
    }
    
    private int mapDragOperationFromModifiers(MouseEvent me, TransferHandler th) {
        if (th == null || !SwingUtilities.isLeftMouseButton(me)) {
            return TransferHandler.NONE;
        }
        return SunDragSourceContextPeer.convertModifiersToDropAction(me.getModifiersEx(), th.getSourceActions(component));
    }
    
    private boolean mousePressedImpl(MouseEvent me) {
        component = (JComponent)(JComponent)me.getSource();
        if (mapDragOperationFromModifiers(me, component.getTransferHandler()) != TransferHandler.NONE) {
            motionThreshold = DragSource.getDragThreshold();
            dndArmedEvent = me;
            return true;
        }
        clearState();
        return false;
    }
    
    private MouseEvent mouseReleasedImpl(MouseEvent me) {
        if (dndArmedEvent == null) {
            return null;
        }
        MouseEvent retEvent = null;
        if (me.getSource() == component) {
            retEvent = dndArmedEvent;
        }
        clearState();
        return retEvent;
    }
    
    private boolean mouseDraggedImpl(MouseEvent me, DragRecognitionSupport$BeforeDrag bd) {
        if (dndArmedEvent == null) {
            return false;
        }
        if (me.getSource() != component) {
            clearState();
            return false;
        }
        int dx = Math.abs(me.getX() - dndArmedEvent.getX());
        int dy = Math.abs(me.getY() - dndArmedEvent.getY());
        if ((dx > motionThreshold) || (dy > motionThreshold)) {
            TransferHandler th = component.getTransferHandler();
            int action = mapDragOperationFromModifiers(me, th);
            if (action != TransferHandler.NONE) {
                if (bd != null) {
                    bd.dragStarting(dndArmedEvent);
                }
                th.exportAsDrag(component, dndArmedEvent, action);
                clearState();
            }
        }
        return true;
    }
}
