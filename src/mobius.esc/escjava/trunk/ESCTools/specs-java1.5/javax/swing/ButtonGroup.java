package javax.swing;

import java.awt.event.*;
import java.util.Vector;
import java.util.Enumeration;
import java.io.Serializable;

public class ButtonGroup implements Serializable {
    protected Vector buttons = new Vector();
    ButtonModel selection = null;
    
    public ButtonGroup() {
        
    }
    
    public void add(AbstractButton b) {
        if (b == null) {
            return;
        }
        buttons.addElement(b);
        if (b.isSelected()) {
            if (selection == null) {
                selection = b.getModel();
            } else {
                b.setSelected(false);
            }
        }
        b.getModel().setGroup(this);
    }
    
    public void remove(AbstractButton b) {
        if (b == null) {
            return;
        }
        buttons.removeElement(b);
        if (b.getModel() == selection) {
            selection = null;
        }
        b.getModel().setGroup(null);
    }
    
    public Enumeration getElements() {
        return buttons.elements();
    }
    
    public ButtonModel getSelection() {
        return selection;
    }
    
    public void setSelected(ButtonModel m, boolean b) {
        if (b && m != null && m != selection) {
            ButtonModel oldSelection = selection;
            selection = m;
            if (oldSelection != null) {
                oldSelection.setSelected(false);
            }
            m.setSelected(true);
        }
    }
    
    public boolean isSelected(ButtonModel m) {
        return (m == selection);
    }
    
    public int getButtonCount() {
        if (buttons == null) {
            return 0;
        } else {
            return buttons.size();
        }
    }
}
