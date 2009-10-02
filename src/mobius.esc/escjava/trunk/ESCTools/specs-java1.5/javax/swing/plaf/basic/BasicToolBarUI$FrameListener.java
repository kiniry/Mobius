package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.border.*;
import javax.swing.plaf.*;

public class BasicToolBarUI$FrameListener extends WindowAdapter {
    /*synthetic*/ final BasicToolBarUI this$0;
    
    protected BasicToolBarUI$FrameListener(/*synthetic*/ final BasicToolBarUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void windowClosing(WindowEvent w) {
        if (this$0.toolBar.isFloatable() == true) {
            if (this$0.dragWindow != null) this$0.dragWindow.setVisible(false);
            BasicToolBarUI.access$202(this$0, false);
            if (BasicToolBarUI.access$300(this$0) == null) BasicToolBarUI.access$302(this$0, this$0.createFloatingWindow(this$0.toolBar));
            if (BasicToolBarUI.access$300(this$0) instanceof Window) ((Window)(Window)BasicToolBarUI.access$300(this$0)).setVisible(false);
            BasicToolBarUI.access$300(this$0).getContentPane().remove(this$0.toolBar);
            String constraint = this$0.constraintBeforeFloating;
            if (this$0.toolBar.getOrientation() == JToolBar.HORIZONTAL) {
                if (constraint == "West" || constraint == "East") {
                    constraint = "North";
                }
            } else {
                if (constraint == "North" || constraint == "South") {
                    constraint = "West";
                }
            }
            if (BasicToolBarUI.access$400(this$0) == null) BasicToolBarUI.access$402(this$0, this$0.toolBar.getParent());
            if (this$0.propertyListener != null) UIManager.removePropertyChangeListener(this$0.propertyListener);
            BasicToolBarUI.access$400(this$0).add(this$0.toolBar, constraint);
            BasicToolBarUI.access$400(this$0).invalidate();
            Container dockingSourceParent = BasicToolBarUI.access$400(this$0).getParent();
            if (dockingSourceParent != null) dockingSourceParent.validate();
            BasicToolBarUI.access$400(this$0).repaint();
        }
    }
}
