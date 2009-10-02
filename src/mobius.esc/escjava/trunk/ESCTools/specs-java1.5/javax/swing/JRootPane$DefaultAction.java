package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.accessibility.*;
import javax.swing.border.*;

class JRootPane$DefaultAction extends AbstractAction {
    JButton owner;
    JRootPane root;
    boolean press;
    
    JRootPane$DefaultAction(JRootPane root, boolean press) {
        
        this.root = root;
        this.press = press;
    }
    
    public void setOwner(JButton owner) {
        this.owner = owner;
    }
    
    public void actionPerformed(ActionEvent e) {
        if (owner != null && SwingUtilities.getRootPane(owner) == root) {
            ButtonModel model = owner.getModel();
            if (press) {
                model.setArmed(true);
                model.setPressed(true);
            } else {
                model.setPressed(false);
            }
        }
    }
    
    public boolean isEnabled() {
        return owner.getModel().isEnabled();
    }
}
