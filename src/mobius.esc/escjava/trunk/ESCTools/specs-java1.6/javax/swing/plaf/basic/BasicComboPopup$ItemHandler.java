package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;

public class BasicComboPopup$ItemHandler implements ItemListener {
    /*synthetic*/ final BasicComboPopup this$0;
    
    protected BasicComboPopup$ItemHandler(/*synthetic*/ final BasicComboPopup this$0) {
        this.this$0 = this$0;
        
    }
    
    public void itemStateChanged(ItemEvent e) {
        BasicComboPopup.access$200(this$0).itemStateChanged(e);
    }
}
