package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.io.ObjectOutputStream;
import java.io.IOException;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JCheckBoxMenuItem extends JMenuItem implements SwingConstants, Accessible {
    private static final String uiClassID = "CheckBoxMenuItemUI";
    
    public JCheckBoxMenuItem() {
        this(null, null, false);
    }
    
    public JCheckBoxMenuItem(Icon icon) {
        this(null, icon, false);
    }
    
    public JCheckBoxMenuItem(String text) {
        this(text, null, false);
    }
    
    public JCheckBoxMenuItem(Action a) {
        this();
        setAction(a);
    }
    
    public JCheckBoxMenuItem(String text, Icon icon) {
        this(text, icon, false);
    }
    
    public JCheckBoxMenuItem(String text, boolean b) {
        this(text, null, b);
    }
    
    public JCheckBoxMenuItem(String text, Icon icon, boolean b) {
        super(text, icon);
        setModel(new JToggleButton$ToggleButtonModel());
        setSelected(b);
        setFocusable(false);
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    public boolean getState() {
        return isSelected();
    }
    
    public synchronized void setState(boolean b) {
        setSelected(b);
    }
    
    public Object[] getSelectedObjects() {
        if (isSelected() == false) return null;
        Object[] selectedObjects = new Object[1];
        selectedObjects[0] = getText();
        return selectedObjects;
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        if (getUIClassID().equals(uiClassID)) {
            byte count = JComponent.getWriteObjCounter(this);
            JComponent.setWriteObjCounter(this, --count);
            if (count == 0 && ui != null) {
                ui.installUI(this);
            }
        }
    }
    
    protected String paramString() {
        return super.paramString();
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JCheckBoxMenuItem$AccessibleJCheckBoxMenuItem(this);
        }
        return accessibleContext;
    }
    {
    }
}
