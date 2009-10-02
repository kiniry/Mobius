package javax.swing;

import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.ObjectOutputStream;
import java.io.IOException;

public class JToolTip extends JComponent implements Accessible {
    private static final String uiClassID = "ToolTipUI";
    String tipText;
    JComponent component;
    
    public JToolTip() {
        
        setOpaque(true);
        updateUI();
    }
    
    public ToolTipUI getUI() {
        return (ToolTipUI)(ToolTipUI)ui;
    }
    
    public void updateUI() {
        setUI((ToolTipUI)(ToolTipUI)UIManager.getUI(this));
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    public void setTipText(String tipText) {
        String oldValue = this.tipText;
        this.tipText = tipText;
        firePropertyChange("tiptext", oldValue, tipText);
    }
    
    public String getTipText() {
        return tipText;
    }
    
    public void setComponent(JComponent c) {
        JComponent oldValue = this.component;
        component = c;
        firePropertyChange("component", oldValue, c);
    }
    
    public JComponent getComponent() {
        return component;
    }
    
    boolean alwaysOnTop() {
        return true;
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
        String tipTextString = (tipText != null ? tipText : "");
        return super.paramString() + ",tipText=" + tipTextString;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JToolTip$AccessibleJToolTip(this);
        }
        return accessibleContext;
    }
    {
    }
}
