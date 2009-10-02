package javax.swing;

import java.util.Vector;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.io.ObjectInputStream;
import java.io.ObjectInputValidation;
import java.io.InvalidObjectException;
import javax.swing.border.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

class JComponent$ReadObjectCallback implements ObjectInputValidation {
    
    /*synthetic*/ static void access$200(JComponent$ReadObjectCallback x0, JComponent x1) {
        x0.registerComponent(x1);
    }
    /*synthetic*/ final JComponent this$0;
    private final Vector roots = new Vector(1);
    private final ObjectInputStream inputStream;
    
    JComponent$ReadObjectCallback(/*synthetic*/ final JComponent this$0, ObjectInputStream s) throws Exception {
        this.this$0 = this$0;
        
        inputStream = s;
        s.registerValidation(this, 0);
    }
    
    public void validateObject() throws InvalidObjectException {
        try {
            for (int i = 0; i < roots.size(); i++) {
                JComponent root = (JComponent)((JComponent)roots.elementAt(i));
                SwingUtilities.updateComponentTreeUI(root);
            }
        } finally {
            JComponent.access$100().remove(inputStream);
        }
    }
    
    private void registerComponent(JComponent c) {
        for (int i = 0; i < roots.size(); i++) {
            JComponent root = (JComponent)(JComponent)roots.elementAt(i);
            for (Component p = c; p != null; p = p.getParent()) {
                if (p == root) {
                    return;
                }
            }
        }
        for (int i = 0; i < roots.size(); i++) {
            JComponent root = (JComponent)(JComponent)roots.elementAt(i);
            for (Component p = root.getParent(); p != null; p = p.getParent()) {
                if (p == c) {
                    roots.removeElementAt(i--);
                    break;
                }
            }
        }
        roots.addElement(c);
    }
}
