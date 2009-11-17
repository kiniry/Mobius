package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.ObjectOutputStream;
import java.io.IOException;

public class JRadioButton extends JToggleButton implements Accessible {
    private static final String uiClassID = "RadioButtonUI";
    
    public JRadioButton() {
        this(null, null, false);
    }
    
    public JRadioButton(Icon icon) {
        this(null, icon, false);
    }
    
    public JRadioButton(Action a) {
        this();
        setAction(a);
    }
    
    public JRadioButton(Icon icon, boolean selected) {
        this(null, icon, selected);
    }
    
    public JRadioButton(String text) {
        this(text, null, false);
    }
    
    public JRadioButton(String text, boolean selected) {
        this(text, null, selected);
    }
    
    public JRadioButton(String text, Icon icon) {
        this(text, icon, false);
    }
    
    public JRadioButton(String text, Icon icon, boolean selected) {
        super(text, icon, selected);
        setBorderPainted(false);
        setHorizontalAlignment(LEADING);
    }
    
    public void updateUI() {
        setUI((ButtonUI)(ButtonUI)UIManager.getUI(this));
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    protected void configurePropertiesFromAction(Action a) {
        String[] types = {Action.MNEMONIC_KEY, Action.NAME, Action.SHORT_DESCRIPTION, Action.ACTION_COMMAND_KEY, "enabled"};
        configurePropertiesFromAction(a, types);
    }
    
    protected PropertyChangeListener createActionPropertyChangeListener(Action a) {
        return new JRadioButton$1(this, this, a);
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
            accessibleContext = new JRadioButton$AccessibleJRadioButton(this);
        }
        return accessibleContext;
    }
    {
    }
}
