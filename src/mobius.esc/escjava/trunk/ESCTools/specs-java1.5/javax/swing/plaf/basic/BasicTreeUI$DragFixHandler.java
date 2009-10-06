package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.dnd.*;
import java.beans.*;
import java.io.*;
import javax.swing.tree.*;
import javax.swing.plaf.basic.DragRecognitionSupport.BeforeDrag;
import com.sun.java.swing.SwingUtilities2;

class BasicTreeUI$DragFixHandler extends BasicTreeUI$Handler implements MouseMotionListener, DragRecognitionSupport$BeforeDrag {
    
    /*synthetic*/ BasicTreeUI$DragFixHandler(BasicTreeUI x0, javax.swing.plaf.basic.BasicTreeUI$1 x1) {
        this(x0);
    }
    /*synthetic*/ final BasicTreeUI this$0;
    
    private BasicTreeUI$DragFixHandler(/*synthetic*/ final BasicTreeUI this$0) {
        super(this$0, null);
        this.this$0 = this$0;
    }
    private boolean dragPressDidSelection;
    private boolean dragStarted;
    private TreePath pressedPath;
    private MouseEvent pressedEvent;
    private boolean valueChangedOnPress;
    
    private boolean isActualPath(TreePath path, int x, int y) {
        if (path == null) {
            return false;
        }
        Rectangle bounds = this$0.getPathBounds(this$0.tree, path);
        if (y > (bounds.y + bounds.height)) {
            return false;
        }
        return (x >= bounds.x) && (x <= (bounds.x + bounds.width));
    }
    
    public void mousePressed(MouseEvent e) {
        if (SwingUtilities2.shouldIgnore(e, this$0.tree)) {
            return;
        }
        if (this$0.isEditing(this$0.tree) && this$0.tree.getInvokesStopCellEditing() && !this$0.stopEditing(this$0.tree)) {
            return;
        }
        this$0.completeEditing();
        pressedPath = this$0.getClosestPathForLocation(this$0.tree, e.getX(), e.getY());
        if (this$0.tree.getDragEnabled()) {
            mousePressedDND(e);
        } else {
            SwingUtilities2.adjustFocus(this$0.tree);
            handleSelectionImpl(e, pressedPath);
        }
    }
    
    private void mousePressedDND(MouseEvent e) {
        pressedEvent = e;
        boolean grabFocus = true;
        dragStarted = false;
        valueChangedOnPress = false;
        if (isActualPath(pressedPath, e.getX(), e.getY()) && DragRecognitionSupport.mousePressed(e)) {
            dragPressDidSelection = false;
            if (e.isControlDown()) {
                return;
            } else if (!e.isShiftDown() && this$0.tree.isPathSelected(pressedPath)) {
                BasicTreeUI.access$1900(this$0, pressedPath);
                BasicTreeUI.access$2100(this$0, pressedPath, true);
                return;
            }
            dragPressDidSelection = true;
            grabFocus = false;
        }
        if (grabFocus) {
            SwingUtilities2.adjustFocus(this$0.tree);
        }
        handleSelectionImpl(e, pressedPath);
    }
    
    public void dragStarting(MouseEvent me) {
        dragStarted = true;
        if (me.isControlDown()) {
            this$0.tree.addSelectionPath(pressedPath);
            BasicTreeUI.access$1900(this$0, pressedPath);
            BasicTreeUI.access$2100(this$0, pressedPath, true);
        }
        pressedEvent = null;
        pressedPath = null;
    }
    
    public void mouseDragged(MouseEvent e) {
        if (SwingUtilities2.shouldIgnore(e, this$0.tree)) {
            return;
        }
        if (this$0.tree.getDragEnabled()) {
            DragRecognitionSupport.mouseDragged(e, this);
        }
    }
    
    public void mouseReleased(MouseEvent e) {
        if (SwingUtilities2.shouldIgnore(e, this$0.tree)) {
            return;
        }
        if (this$0.tree.getDragEnabled()) {
            mouseReleasedDND(e);
        }
        pressedEvent = null;
        pressedPath = null;
    }
    
    private void mouseReleasedDND(MouseEvent e) {
        MouseEvent me = DragRecognitionSupport.mouseReleased(e);
        if (me != null) {
            SwingUtilities2.adjustFocus(this$0.tree);
            if (!dragPressDidSelection) {
                handleSelectionImpl(me, pressedPath);
            }
        }
        if (!dragStarted) {
            if (pressedPath != null && !valueChangedOnPress && isActualPath(pressedPath, pressedEvent.getX(), pressedEvent.getY())) {
                BasicTreeUI.access$2200(this$0, pressedPath, pressedEvent, e);
            }
        }
    }
    
    public void valueChanged(TreeSelectionEvent event) {
        valueChangedOnPress = true;
        super.valueChanged(event);
    }
}
