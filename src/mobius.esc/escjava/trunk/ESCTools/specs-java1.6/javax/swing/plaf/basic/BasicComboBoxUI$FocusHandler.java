package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.accessibility.*;
import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.swing.text.*;
import javax.swing.event.*;

public class BasicComboBoxUI$FocusHandler implements FocusListener {
    /*synthetic*/ final BasicComboBoxUI this$0;
    
    public BasicComboBoxUI$FocusHandler(/*synthetic*/ final BasicComboBoxUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void focusGained(FocusEvent e) {
        BasicComboBoxUI.access$100(this$0).focusGained(e);
    }
    
    public void focusLost(FocusEvent e) {
        BasicComboBoxUI.access$100(this$0).focusLost(e);
    }
}
