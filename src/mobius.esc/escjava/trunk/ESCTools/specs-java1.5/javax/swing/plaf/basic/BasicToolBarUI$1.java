package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.border.*;
import javax.swing.plaf.*;

class BasicToolBarUI$1 extends JFrame {
    /*synthetic*/ final BasicToolBarUI this$0;
    
    BasicToolBarUI$1(/*synthetic*/ final BasicToolBarUI this$0, .java.lang.String x0, .java.awt.GraphicsConfiguration x1) {
        this.this$0 = this$0;
        super(x0, x1);
    }
    
    protected JRootPane createRootPane() {
        JRootPane rootPane = new BasicToolBarUI$1$1(this);
        rootPane.setOpaque(true);
        return rootPane;
    }
}
