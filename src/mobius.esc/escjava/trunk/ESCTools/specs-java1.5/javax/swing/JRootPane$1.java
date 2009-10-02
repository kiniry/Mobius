package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.accessibility.*;
import javax.swing.border.*;

class JRootPane$1 extends BorderLayout {
    /*synthetic*/ final JRootPane this$0;
    
    JRootPane$1(/*synthetic*/ final JRootPane this$0) {
        this.this$0 = this$0;
        
    }
    
    public void addLayoutComponent(Component comp, Object constraints) {
        if (constraints == null) {
            constraints = BorderLayout.CENTER;
        }
        super.addLayoutComponent(comp, constraints);
    }
}
