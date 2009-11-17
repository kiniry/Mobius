package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.border.*;
import javax.swing.plaf.*;

public class BasicToolBarUI$ToolBarFocusListener implements FocusListener {
    /*synthetic*/ final BasicToolBarUI this$0;
    
    protected BasicToolBarUI$ToolBarFocusListener(/*synthetic*/ final BasicToolBarUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void focusGained(FocusEvent e) {
        BasicToolBarUI.access$500(this$0).focusGained(e);
    }
    
    public void focusLost(FocusEvent e) {
        BasicToolBarUI.access$500(this$0).focusLost(e);
    }
}
