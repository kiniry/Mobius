package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;

class BasicSplitPaneUI$Handler implements FocusListener, PropertyChangeListener {
    
    /*synthetic*/ BasicSplitPaneUI$Handler(BasicSplitPaneUI x0, javax.swing.plaf.basic.BasicSplitPaneUI$1 x1) {
        this(x0);
    }
    /*synthetic*/ final BasicSplitPaneUI this$0;
    
    private BasicSplitPaneUI$Handler(/*synthetic*/ final BasicSplitPaneUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        if (e.getSource() == this$0.splitPane) {
            String changeName = e.getPropertyName();
            if (changeName == JSplitPane.ORIENTATION_PROPERTY) {
                BasicSplitPaneUI.access$302(this$0, this$0.splitPane.getOrientation());
                this$0.resetLayoutManager();
            } else if (changeName == JSplitPane.CONTINUOUS_LAYOUT_PROPERTY) {
                this$0.setContinuousLayout(this$0.splitPane.isContinuousLayout());
                if (!this$0.isContinuousLayout()) {
                    if (this$0.nonContinuousLayoutDivider == null) {
                        this$0.setNonContinuousLayoutDivider(this$0.createDefaultNonContinuousLayoutDivider(), true);
                    } else if (this$0.nonContinuousLayoutDivider.getParent() == null) {
                        this$0.setNonContinuousLayoutDivider(this$0.nonContinuousLayoutDivider, true);
                    }
                }
            } else if (changeName == JSplitPane.DIVIDER_SIZE_PROPERTY) {
                this$0.divider.setDividerSize(this$0.splitPane.getDividerSize());
                this$0.dividerSize = this$0.divider.getDividerSize();
                this$0.splitPane.revalidate();
                this$0.splitPane.repaint();
            }
        }
    }
    
    public void focusGained(FocusEvent ev) {
        BasicSplitPaneUI.access$202(this$0, true);
        this$0.splitPane.repaint();
    }
    
    public void focusLost(FocusEvent ev) {
        BasicSplitPaneUI.access$202(this$0, false);
        this$0.splitPane.repaint();
    }
}
