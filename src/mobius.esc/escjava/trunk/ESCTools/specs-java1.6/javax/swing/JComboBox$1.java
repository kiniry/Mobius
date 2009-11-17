package javax.swing;

import java.beans.*;
import java.util.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.accessibility.*;

class JComboBox$1 implements AncestorListener {
    /*synthetic*/ final JComboBox this$0;
    
    JComboBox$1(/*synthetic*/ final JComboBox this$0) {
        this.this$0 = this$0;
        
    }
    
    public void ancestorAdded(AncestorEvent event) {
        this$0.hidePopup();
    }
    
    public void ancestorRemoved(AncestorEvent event) {
        this$0.hidePopup();
    }
    
    public void ancestorMoved(AncestorEvent event) {
        if (event.getSource() != this$0) this$0.hidePopup();
    }
}
