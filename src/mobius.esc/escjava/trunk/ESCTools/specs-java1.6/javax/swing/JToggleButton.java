package javax.swing;

import java.awt.*;
import java.awt.event.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.ObjectOutputStream;
import java.io.IOException;

public class JToggleButton extends AbstractButton implements Accessible {
    private static final String uiClassID = "ToggleButtonUI";
    
    public JToggleButton() {
        this(null, null, false);
    }
    
    public JToggleButton(Icon icon) {
        this(null, icon, false);
    }
    
    public JToggleButton(Icon icon, boolean selected) {
        this(null, icon, selected);
    }
    
    public JToggleButton(String text) {
        this(text, null, false);
    }
    
    public JToggleButton(String text, boolean selected) {
        this(text, null, selected);
    }
    
    public JToggleButton(Action a) {
        this();
        setAction(a);
    }
    
    public JToggleButton(String text, Icon icon) {
        this(text, icon, false);
    }
    
    public JToggleButton(String text, Icon icon, boolean selected) {
        
        setModel(new JToggleButton$ToggleButtonModel());
        model.setSelected(selected);
        init(text, icon);
    }
    
    public void updateUI() {
        setUI((ButtonUI)(ButtonUI)UIManager.getUI(this));
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    {
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
            accessibleContext = new JToggleButton$AccessibleJToggleButton(this);
        }
        return accessibleContext;
    }
    {
    }
}
