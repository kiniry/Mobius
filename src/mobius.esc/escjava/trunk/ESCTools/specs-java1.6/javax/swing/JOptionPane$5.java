package javax.swing;

import java.awt.Container;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.lang.reflect.Method;
import java.lang.reflect.InvocationTargetException;
import java.security.AccessController;
import javax.accessibility.*;

class JOptionPane$5 implements PropertyChangeListener {
    /*synthetic*/ final JOptionPane this$0;
    /*synthetic*/ final JInternalFrame val$iFrame;
    
    JOptionPane$5(/*synthetic*/ final JOptionPane this$0, /*synthetic*/ final JInternalFrame val$iFrame) {
        this.this$0 = this$0;
        this.val$iFrame = val$iFrame;
        
    }
    
    public void propertyChange(PropertyChangeEvent event) {
        if (val$iFrame.isVisible() && event.getSource() == this$0 && event.getPropertyName().equals("value")) {
            try {
                Object obj;
                obj = AccessController.doPrivileged(new JOptionPane$ModalPrivilegedAction(Container.class, "stopLWModal"));
                if (obj != null) {
                    ((Method)(Method)obj).invoke(val$iFrame, null);
                }
            } catch (IllegalAccessException ex) {
            } catch (IllegalArgumentException ex) {
            } catch (InvocationTargetException ex) {
            }
            try {
                val$iFrame.setClosed(true);
            } catch (java.beans.PropertyVetoException e) {
            }
            val$iFrame.setVisible(false);
        }
    }
}
