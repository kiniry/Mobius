package javax.swing;

import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.ObjectOutputStream;
import java.io.IOException;

public class JSeparator extends JComponent implements SwingConstants, Accessible {
    private static final String uiClassID = "SeparatorUI";
    private int orientation = HORIZONTAL;
    
    public JSeparator() {
        this(HORIZONTAL);
    }
    
    public JSeparator(int orientation) {
        
        checkOrientation(orientation);
        this.orientation = orientation;
        setFocusable(false);
        updateUI();
    }
    
    public SeparatorUI getUI() {
        return (SeparatorUI)(SeparatorUI)ui;
    }
    
    public void setUI(SeparatorUI ui) {
        super.setUI(ui);
    }
    
    public void updateUI() {
        setUI((SeparatorUI)(SeparatorUI)UIManager.getUI(this));
    }
    
    public String getUIClassID() {
        return uiClassID;
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
    
    public int getOrientation() {
        return this.orientation;
    }
    
    public void setOrientation(int orientation) {
        if (this.orientation == orientation) {
            return;
        }
        int oldValue = this.orientation;
        checkOrientation(orientation);
        this.orientation = orientation;
        firePropertyChange("orientation", oldValue, orientation);
        revalidate();
        repaint();
    }
    
    private void checkOrientation(int orientation) {
        switch (orientation) {
        case VERTICAL: 
        
        case HORIZONTAL: 
            break;
        
        default: 
            throw new IllegalArgumentException("orientation must be one of: VERTICAL, HORIZONTAL");
        
        }
    }
    
    protected String paramString() {
        String orientationString = (orientation == HORIZONTAL ? "HORIZONTAL" : "VERTICAL");
        return super.paramString() + ",orientation=" + orientationString;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JSeparator$AccessibleJSeparator(this);
        }
        return accessibleContext;
    }
    {
    }
}
