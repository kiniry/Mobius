package javax.swing.plaf.basic;

import java.awt.event.*;
import java.awt.dnd.DragSource;
import javax.swing.*;
import sun.awt.dnd.SunDragSourceContextPeer;

class BasicDragGestureRecognizer implements MouseListener, MouseMotionListener {
    
    BasicDragGestureRecognizer() {
        
    }
    private MouseEvent dndArmedEvent = null;
    
    private static int getMotionThreshold() {
        return DragSource.getDragThreshold();
    }
    
    protected int mapDragOperationFromModifiers(MouseEvent e) {
        int mods = e.getModifiersEx();
        if ((mods & InputEvent.BUTTON1_DOWN_MASK) != InputEvent.BUTTON1_DOWN_MASK) {
            return TransferHandler.NONE;
        }
        JComponent c = getComponent(e);
        TransferHandler th = c.getTransferHandler();
        return SunDragSourceContextPeer.convertModifiersToDropAction(mods, th.getSourceActions(c));
    }
    
    public void mouseClicked(MouseEvent e) {
    }
    
    public void mousePressed(MouseEvent e) {
        dndArmedEvent = null;
        if (isDragPossible(e) && mapDragOperationFromModifiers(e) != TransferHandler.NONE) {
            dndArmedEvent = e;
            e.consume();
        }
    }
    
    public void mouseReleased(MouseEvent e) {
        dndArmedEvent = null;
    }
    
    public void mouseEntered(MouseEvent e) {
    }
    
    public void mouseExited(MouseEvent e) {
    }
    
    public void mouseDragged(MouseEvent e) {
        if (dndArmedEvent != null) {
            e.consume();
            int action = mapDragOperationFromModifiers(e);
            if (action == TransferHandler.NONE) {
                return;
            }
            int dx = Math.abs(e.getX() - dndArmedEvent.getX());
            int dy = Math.abs(e.getY() - dndArmedEvent.getY());
            if ((dx > getMotionThreshold()) || (dy > getMotionThreshold())) {
                JComponent c = getComponent(e);
                TransferHandler th = c.getTransferHandler();
                th.exportAsDrag(c, dndArmedEvent, action);
                dndArmedEvent = null;
            }
        }
    }
    
    public void mouseMoved(MouseEvent e) {
    }
    
    private TransferHandler getTransferHandler(MouseEvent e) {
        JComponent c = getComponent(e);
        return c == null ? null : c.getTransferHandler();
    }
    
    protected boolean isDragPossible(MouseEvent e) {
        JComponent c = getComponent(e);
        return (c == null) ? true : (c.getTransferHandler() != null);
    }
    
    protected JComponent getComponent(MouseEvent e) {
        Object src = e.getSource();
        if (src instanceof JComponent) {
            JComponent c = (JComponent)(JComponent)src;
            return c;
        }
        return null;
    }
}
