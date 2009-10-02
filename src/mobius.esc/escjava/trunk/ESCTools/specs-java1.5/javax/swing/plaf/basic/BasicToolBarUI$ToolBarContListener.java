package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.border.*;
import javax.swing.plaf.*;

public class BasicToolBarUI$ToolBarContListener implements ContainerListener {
    /*synthetic*/ final BasicToolBarUI this$0;
    
    protected BasicToolBarUI$ToolBarContListener(/*synthetic*/ final BasicToolBarUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void componentAdded(ContainerEvent e) {
        BasicToolBarUI.access$500(this$0).componentAdded(e);
    }
    
    public void componentRemoved(ContainerEvent e) {
        BasicToolBarUI.access$500(this$0).componentRemoved(e);
    }
}
