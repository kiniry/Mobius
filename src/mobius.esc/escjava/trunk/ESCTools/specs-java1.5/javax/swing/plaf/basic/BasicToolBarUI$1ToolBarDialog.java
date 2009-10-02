package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.border.*;
import javax.swing.plaf.*;

class BasicToolBarUI$1ToolBarDialog extends JDialog {
    /*synthetic*/ final BasicToolBarUI this$0;
    
    public BasicToolBarUI$1ToolBarDialog(/*synthetic*/ final BasicToolBarUI this$0, Frame owner, String title, boolean modal) {
        this.this$0 = this$0;
        super(owner, title, modal);
    }
    
    public BasicToolBarUI$1ToolBarDialog(/*synthetic*/ final BasicToolBarUI this$0, Dialog owner, String title, boolean modal) {
        this.this$0 = this$0;
        super(owner, title, modal);
    }
    
    protected JRootPane createRootPane() {
        JRootPane rootPane = new BasicToolBarUI$1ToolBarDialog$1(this);
        rootPane.setOpaque(true);
        return rootPane;
    }
}
