package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;

public class JCheckBox extends JToggleButton implements Accessible {
    public static final String BORDER_PAINTED_FLAT_CHANGED_PROPERTY = "borderPaintedFlat";
    private boolean flat = false;
    private static final String uiClassID = "CheckBoxUI";
    
    public JCheckBox() {
        this(null, null, false);
    }
    
    public JCheckBox(Icon icon) {
        this(null, icon, false);
    }
    
    public JCheckBox(Icon icon, boolean selected) {
        this(null, icon, selected);
    }
    
    public JCheckBox(String text) {
        this(text, null, false);
    }
    
    public JCheckBox(Action a) {
        this();
        setAction(a);
    }
    
    public JCheckBox(String text, boolean selected) {
        this(text, null, selected);
    }
    
    public JCheckBox(String text, Icon icon) {
        this(text, icon, false);
    }
    
    public JCheckBox(String text, Icon icon, boolean selected) {
        super(text, icon, selected);
        setUIProperty("borderPainted", Boolean.FALSE);
        setHorizontalAlignment(LEADING);
    }
    
    public void setBorderPaintedFlat(boolean b) {
        boolean oldValue = flat;
        flat = b;
        firePropertyChange(BORDER_PAINTED_FLAT_CHANGED_PROPERTY, oldValue, flat);
        if (b != oldValue) {
            revalidate();
            repaint();
        }
    }
    
    public boolean isBorderPaintedFlat() {
        return flat;
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
        return new JCheckBox$1(this, this, a);
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
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        if (getUIClassID().equals(uiClassID)) {
            updateUI();
        }
    }
    
    protected String paramString() {
        return super.paramString();
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JCheckBox$AccessibleJCheckBox(this);
        }
        return accessibleContext;
    }
    {
    }
}
