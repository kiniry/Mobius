package javax.swing;

import javax.swing.event.InternalFrameEvent;
import javax.swing.event.InternalFrameAdapter;
import javax.accessibility.*;

class JOptionPane$4 extends InternalFrameAdapter {
    /*synthetic*/ final JOptionPane this$0;
    
    JOptionPane$4(/*synthetic*/ final JOptionPane this$0) {
        this.this$0 = this$0;
        
    }
    
    public void internalFrameClosing(InternalFrameEvent e) {
        if (this$0.getValue() == JOptionPane.UNINITIALIZED_VALUE) {
            this$0.setValue(null);
        }
    }
}
