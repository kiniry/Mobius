package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import java.beans.*;

public class BasicSplitPaneDivider$DragController {
    /*synthetic*/ final BasicSplitPaneDivider this$0;
    int initialX;
    int maxX;
    int minX;
    int offset;
    
    protected BasicSplitPaneDivider$DragController(/*synthetic*/ final BasicSplitPaneDivider this$0, MouseEvent e) {
        this.this$0 = this$0;
        
        JSplitPane splitPane = this$0.splitPaneUI.getSplitPane();
        Component leftC = splitPane.getLeftComponent();
        Component rightC = splitPane.getRightComponent();
        initialX = this$0.getLocation().x;
        if (e.getSource() == this$0) {
            offset = e.getX();
        } else {
            offset = e.getX() - initialX;
        }
        if (leftC == null || rightC == null || offset < -1 || offset >= this$0.getSize().width) {
            maxX = -1;
        } else {
            Insets insets = splitPane.getInsets();
            if (leftC.isVisible()) {
                minX = leftC.getMinimumSize().width;
                if (insets != null) {
                    minX += insets.left;
                }
            } else {
                minX = 0;
            }
            if (rightC.isVisible()) {
                int right = (insets != null) ? insets.right : 0;
                maxX = Math.max(0, splitPane.getSize().width - (this$0.getSize().width + right) - rightC.getMinimumSize().width);
            } else {
                int right = (insets != null) ? insets.right : 0;
                maxX = Math.max(0, splitPane.getSize().width - (this$0.getSize().width + right));
            }
            if (maxX < minX) minX = maxX = 0;
        }
    }
    
    protected boolean isValid() {
        return (maxX > 0);
    }
    
    protected int positionForMouseEvent(MouseEvent e) {
        int newX = (e.getSource() == this$0) ? (e.getX() + this$0.getLocation().x) : e.getX();
        newX = Math.min(maxX, Math.max(minX, newX - offset));
        return newX;
    }
    
    protected int getNeededLocation(int x, int y) {
        int newX;
        newX = Math.min(maxX, Math.max(minX, x - offset));
        return newX;
    }
    
    protected void continueDrag(int newX, int newY) {
        this$0.dragDividerTo(getNeededLocation(newX, newY));
    }
    
    protected void continueDrag(MouseEvent e) {
        this$0.dragDividerTo(positionForMouseEvent(e));
    }
    
    protected void completeDrag(int x, int y) {
        this$0.finishDraggingTo(getNeededLocation(x, y));
    }
    
    protected void completeDrag(MouseEvent e) {
        this$0.finishDraggingTo(positionForMouseEvent(e));
    }
}
