package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.border.*;
import javax.swing.plaf.*;

class BasicToolBarUI$1$1 extends JRootPane {
    /*synthetic*/ final BasicToolBarUI$1 this$1;
    
    BasicToolBarUI$1$1(/*synthetic*/ final BasicToolBarUI$1 this$1) {
        this.this$1 = this$1;
        
    }
    private boolean packing = false;
    
    public void validate() {
        super.validate();
        if (!packing) {
            packing = true;
            this$1.pack();
            packing = false;
        }
    }
}
