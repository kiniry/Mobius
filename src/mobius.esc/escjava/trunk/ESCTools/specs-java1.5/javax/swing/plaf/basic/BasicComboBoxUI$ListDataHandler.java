package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.accessibility.*;
import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.swing.text.*;
import javax.swing.event.*;

public class BasicComboBoxUI$ListDataHandler implements ListDataListener {
    /*synthetic*/ final BasicComboBoxUI this$0;
    
    public BasicComboBoxUI$ListDataHandler(/*synthetic*/ final BasicComboBoxUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void contentsChanged(ListDataEvent e) {
        BasicComboBoxUI.access$100(this$0).contentsChanged(e);
    }
    
    public void intervalAdded(ListDataEvent e) {
        BasicComboBoxUI.access$100(this$0).intervalAdded(e);
    }
    
    public void intervalRemoved(ListDataEvent e) {
        BasicComboBoxUI.access$100(this$0).intervalRemoved(e);
    }
}
