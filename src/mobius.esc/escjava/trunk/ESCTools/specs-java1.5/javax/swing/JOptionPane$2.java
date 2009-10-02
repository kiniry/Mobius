package javax.swing;

import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import javax.accessibility.*;

class JOptionPane$2 extends ComponentAdapter {
    /*synthetic*/ final JOptionPane this$0;
    
    JOptionPane$2(/*synthetic*/ final JOptionPane this$0) {
        this.this$0 = this$0;
        
    }
    
    public void componentShown(ComponentEvent ce) {
        this$0.setValue(JOptionPane.UNINITIALIZED_VALUE);
    }
}
