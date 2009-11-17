package javax.swing;

import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import javax.accessibility.*;

class JOptionPane$1 extends WindowAdapter {
    /*synthetic*/ final JOptionPane this$0;
    
    JOptionPane$1(/*synthetic*/ final JOptionPane this$0) {
        this.this$0 = this$0;
        
    }
    private boolean gotFocus = false;
    
    public void windowClosing(WindowEvent we) {
        this$0.setValue(null);
    }
    
    public void windowGainedFocus(WindowEvent we) {
        if (!gotFocus) {
            this$0.selectInitialValue();
            gotFocus = true;
        }
    }
}
