package javax.swing;

import java.awt.*;
import java.awt.event.*;
import javax.swing.event.*;
import javax.swing.border.*;
import javax.accessibility.*;

class JViewport$1 implements ActionListener {
    /*synthetic*/ final JViewport this$0;
    
    JViewport$1(/*synthetic*/ final JViewport this$0) {
        this.this$0 = this$0;
        
    }
    
    public void actionPerformed(ActionEvent ae) {
        if (JViewport.access$000(this$0)) {
            this$0.repaint();
        }
    }
}
