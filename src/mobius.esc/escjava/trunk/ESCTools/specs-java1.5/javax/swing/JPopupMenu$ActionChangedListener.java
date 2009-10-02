package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.io.Serializable;
import java.beans.*;
import javax.accessibility.*;
import javax.swing.event.*;

class JPopupMenu$ActionChangedListener implements PropertyChangeListener, Serializable {
    /*synthetic*/ final JPopupMenu this$0;
    private JMenuItem menuItem;
    
    public JPopupMenu$ActionChangedListener(/*synthetic*/ final JPopupMenu this$0, JMenuItem mi) {
        this.this$0 = this$0;
        
        setTarget(mi);
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        String propertyName = e.getPropertyName();
        if (e.getPropertyName().equals(Action.NAME)) {
            String text = (String)(String)e.getNewValue();
            menuItem.setText(text);
        } else if (propertyName.equals("enabled")) {
            Boolean enabledState = (Boolean)(Boolean)e.getNewValue();
            menuItem.setEnabled(enabledState.booleanValue());
        } else if (e.getPropertyName().equals(Action.SMALL_ICON)) {
            Icon icon = (Icon)(Icon)e.getNewValue();
            menuItem.setIcon(icon);
            menuItem.invalidate();
            menuItem.repaint();
        }
    }
    
    public void setTarget(JMenuItem b) {
        this.menuItem = b;
    }
}
