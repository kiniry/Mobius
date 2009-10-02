package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import java.beans.*;

public class BasicSplitPaneDivider$MouseHandler extends MouseAdapter implements MouseMotionListener {
    /*synthetic*/ final BasicSplitPaneDivider this$0;
    
    protected BasicSplitPaneDivider$MouseHandler(/*synthetic*/ final BasicSplitPaneDivider this$0) {
        this.this$0 = this$0;
        
    }
    
    public void mousePressed(MouseEvent e) {
        if ((e.getSource() == this$0 || e.getSource() == this$0.splitPane) && this$0.dragger == null && this$0.splitPane.isEnabled()) {
            Component newHiddenDivider = this$0.splitPaneUI.getNonContinuousLayoutDivider();
            if (this$0.hiddenDivider != newHiddenDivider) {
                if (this$0.hiddenDivider != null) {
                    this$0.hiddenDivider.removeMouseListener(this);
                    this$0.hiddenDivider.removeMouseMotionListener(this);
                }
                this$0.hiddenDivider = newHiddenDivider;
                if (this$0.hiddenDivider != null) {
                    this$0.hiddenDivider.addMouseMotionListener(this);
                    this$0.hiddenDivider.addMouseListener(this);
                }
            }
            if (this$0.splitPane.getLeftComponent() != null && this$0.splitPane.getRightComponent() != null) {
                if (this$0.orientation == JSplitPane.HORIZONTAL_SPLIT) {
                    this$0.dragger = new BasicSplitPaneDivider$DragController(this$0, e);
                } else {
                    this$0.dragger = new BasicSplitPaneDivider$VerticalDragController(this$0, e);
                }
                if (!this$0.dragger.isValid()) {
                    this$0.dragger = null;
                } else {
                    this$0.prepareForDragging();
                    this$0.dragger.continueDrag(e);
                }
            }
            e.consume();
        }
    }
    
    public void mouseReleased(MouseEvent e) {
        if (this$0.dragger != null) {
            if (e.getSource() == this$0.splitPane) {
                this$0.dragger.completeDrag(e.getX(), e.getY());
            } else if (e.getSource() == this$0) {
                Point ourLoc = this$0.getLocation();
                this$0.dragger.completeDrag(e.getX() + ourLoc.x, e.getY() + ourLoc.y);
            } else if (e.getSource() == this$0.hiddenDivider) {
                Point hDividerLoc = this$0.hiddenDivider.getLocation();
                int ourX = e.getX() + hDividerLoc.x;
                int ourY = e.getY() + hDividerLoc.y;
                this$0.dragger.completeDrag(ourX, ourY);
            }
            this$0.dragger = null;
            e.consume();
        }
    }
    
    public void mouseDragged(MouseEvent e) {
        if (this$0.dragger != null) {
            if (e.getSource() == this$0.splitPane) {
                this$0.dragger.continueDrag(e.getX(), e.getY());
            } else if (e.getSource() == this$0) {
                Point ourLoc = this$0.getLocation();
                this$0.dragger.continueDrag(e.getX() + ourLoc.x, e.getY() + ourLoc.y);
            } else if (e.getSource() == this$0.hiddenDivider) {
                Point hDividerLoc = this$0.hiddenDivider.getLocation();
                int ourX = e.getX() + hDividerLoc.x;
                int ourY = e.getY() + hDividerLoc.y;
                this$0.dragger.continueDrag(ourX, ourY);
            }
            e.consume();
        }
    }
    
    public void mouseMoved(MouseEvent e) {
    }
    
    public void mouseEntered(MouseEvent e) {
        if (e.getSource() == this$0) {
            this$0.setMouseOver(true);
        }
    }
    
    public void mouseExited(MouseEvent e) {
        if (e.getSource() == this$0) {
            this$0.setMouseOver(false);
        }
    }
}
