package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import java.beans.*;

public class BasicSplitPaneDivider$VerticalDragController extends BasicSplitPaneDivider$DragController {
    /*synthetic*/ final BasicSplitPaneDivider this$0;
    
    protected BasicSplitPaneDivider$VerticalDragController(/*synthetic*/ final BasicSplitPaneDivider this$0, MouseEvent e) {
        super(this$0, e);
        this.this$0 = this$0;
        JSplitPane splitPane = this$0.splitPaneUI.getSplitPane();
        Component leftC = splitPane.getLeftComponent();
        Component rightC = splitPane.getRightComponent();
        initialX = this$0.getLocation().y;
        if (e.getSource() == this$0) {
            offset = e.getY();
        } else {
            offset = e.getY() - initialX;
        }
        if (leftC == null || rightC == null || offset < -1 || offset > this$0.getSize().height) {
            maxX = -1;
        } else {
            Insets insets = splitPane.getInsets();
            if (leftC.isVisible()) {
                minX = leftC.getMinimumSize().height;
                if (insets != null) {
                    minX += insets.top;
                }
            } else {
                minX = 0;
            }
            if (rightC.isVisible()) {
                int bottom = (insets != null) ? insets.bottom : 0;
                maxX = Math.max(0, splitPane.getSize().height - (this$0.getSize().height + bottom) - rightC.getMinimumSize().height);
            } else {
                int bottom = (insets != null) ? insets.bottom : 0;
                maxX = Math.max(0, splitPane.getSize().height - (this$0.getSize().height + bottom));
            }
            if (maxX < minX) minX = maxX = 0;
        }
    }
    
    protected int getNeededLocation(int x, int y) {
        int newY;
        newY = Math.min(maxX, Math.max(minX, y - offset));
        return newY;
    }
    
    protected int positionForMouseEvent(MouseEvent e) {
        int newY = (e.getSource() == this$0) ? (e.getY() + this$0.getLocation().y) : e.getY();
        newY = Math.min(maxX, Math.max(minX, newY - offset));
        return newY;
    }
}
