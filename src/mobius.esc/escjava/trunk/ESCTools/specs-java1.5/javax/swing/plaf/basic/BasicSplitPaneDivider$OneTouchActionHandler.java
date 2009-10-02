package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import java.beans.*;

class BasicSplitPaneDivider$OneTouchActionHandler implements ActionListener {
    /*synthetic*/ final BasicSplitPaneDivider this$0;
    private boolean toMinimum;
    
    BasicSplitPaneDivider$OneTouchActionHandler(/*synthetic*/ final BasicSplitPaneDivider this$0, boolean toMinimum) {
        this.this$0 = this$0;
        
        this.toMinimum = toMinimum;
    }
    
    public void actionPerformed(ActionEvent e) {
        Insets insets = this$0.splitPane.getInsets();
        int lastLoc = this$0.splitPane.getLastDividerLocation();
        int currentLoc = this$0.splitPaneUI.getDividerLocation(this$0.splitPane);
        int newLoc;
        if (toMinimum) {
            if (this$0.orientation == JSplitPane.VERTICAL_SPLIT) {
                if (currentLoc >= (this$0.splitPane.getHeight() - insets.bottom - this$0.getHeight())) {
                    int maxLoc = this$0.splitPane.getMaximumDividerLocation();
                    newLoc = Math.min(lastLoc, maxLoc);
                    this$0.splitPaneUI.setKeepHidden(false);
                } else {
                    newLoc = insets.top;
                    this$0.splitPaneUI.setKeepHidden(true);
                }
            } else {
                if (currentLoc >= (this$0.splitPane.getWidth() - insets.right - this$0.getWidth())) {
                    int maxLoc = this$0.splitPane.getMaximumDividerLocation();
                    newLoc = Math.min(lastLoc, maxLoc);
                    this$0.splitPaneUI.setKeepHidden(false);
                } else {
                    newLoc = insets.left;
                    this$0.splitPaneUI.setKeepHidden(true);
                }
            }
        } else {
            if (this$0.orientation == JSplitPane.VERTICAL_SPLIT) {
                if (currentLoc == insets.top) {
                    int maxLoc = this$0.splitPane.getMaximumDividerLocation();
                    newLoc = Math.min(lastLoc, maxLoc);
                    this$0.splitPaneUI.setKeepHidden(false);
                } else {
                    newLoc = this$0.splitPane.getHeight() - this$0.getHeight() - insets.top;
                    this$0.splitPaneUI.setKeepHidden(true);
                }
            } else {
                if (currentLoc == insets.left) {
                    int maxLoc = this$0.splitPane.getMaximumDividerLocation();
                    newLoc = Math.min(lastLoc, maxLoc);
                    this$0.splitPaneUI.setKeepHidden(false);
                } else {
                    newLoc = this$0.splitPane.getWidth() - this$0.getWidth() - insets.left;
                    this$0.splitPaneUI.setKeepHidden(true);
                }
            }
        }
        if (currentLoc != newLoc) {
            this$0.splitPane.setDividerLocation(newLoc);
            this$0.splitPane.setLastDividerLocation(currentLoc);
        }
    }
}
