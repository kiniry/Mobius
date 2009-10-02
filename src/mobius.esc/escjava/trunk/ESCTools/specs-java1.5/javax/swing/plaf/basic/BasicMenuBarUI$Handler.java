package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.Component;
import java.awt.event.*;
import javax.swing.border.*;
import javax.swing.plaf.*;

class BasicMenuBarUI$Handler implements ChangeListener, ContainerListener {
    
    /*synthetic*/ BasicMenuBarUI$Handler(BasicMenuBarUI x0, javax.swing.plaf.basic.BasicMenuBarUI$1 x1) {
        this(x0);
    }
    /*synthetic*/ final BasicMenuBarUI this$0;
    
    private BasicMenuBarUI$Handler(/*synthetic*/ final BasicMenuBarUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void stateChanged(ChangeEvent e) {
        int i;
        int c;
        for (i = 0, c = this$0.menuBar.getMenuCount(); i < c; i++) {
            JMenu menu = this$0.menuBar.getMenu(i);
            if (menu != null && menu.isSelected()) {
                this$0.menuBar.getSelectionModel().setSelectedIndex(i);
                break;
            }
        }
    }
    
    public void componentAdded(ContainerEvent e) {
        Component c = e.getChild();
        if (c instanceof JMenu) ((JMenu)(JMenu)c).getModel().addChangeListener(this$0.changeListener);
    }
    
    public void componentRemoved(ContainerEvent e) {
        Component c = e.getChild();
        if (c instanceof JMenu) ((JMenu)(JMenu)c).getModel().removeChangeListener(this$0.changeListener);
    }
}
