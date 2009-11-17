package javax.swing;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import javax.accessibility.*;

class JOptionPane$3 implements PropertyChangeListener {
    /*synthetic*/ final JOptionPane this$0;
    /*synthetic*/ final JDialog val$dialog;
    
    JOptionPane$3(/*synthetic*/ final JOptionPane this$0, /*synthetic*/ final JDialog val$dialog) {
        this.this$0 = this$0;
        this.val$dialog = val$dialog;
        
    }
    
    public void propertyChange(PropertyChangeEvent event) {
        if (val$dialog.isVisible() && event.getSource() == this$0 && (event.getPropertyName().equals("value")) && event.getNewValue() != null && event.getNewValue() != JOptionPane.UNINITIALIZED_VALUE) {
            val$dialog.setVisible(false);
        }
    }
}
