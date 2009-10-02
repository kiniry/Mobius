package javax.swing;

import java.awt.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.ObjectOutputStream;
import java.io.IOException;

public class JPanel extends JComponent implements Accessible {
    private static final String uiClassID = "PanelUI";
    
    public JPanel(LayoutManager layout, boolean isDoubleBuffered) {
        
        setLayout(layout);
        setDoubleBuffered(isDoubleBuffered);
        setUIProperty("opaque", Boolean.TRUE);
        updateUI();
    }
    
    public JPanel(LayoutManager layout) {
        this(layout, true);
    }
    
    public JPanel(boolean isDoubleBuffered) {
        this(new FlowLayout(), isDoubleBuffered);
    }
    
    public JPanel() {
        this(true);
    }
    
    public void updateUI() {
        setUI((PanelUI)(PanelUI)UIManager.getUI(this));
    }
    
    public PanelUI getUI() {
        return (PanelUI)(PanelUI)ui;
    }
    
    public void setUI(PanelUI ui) {
        super.setUI(ui);
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
    
    protected String paramString() {
        return super.paramString();
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JPanel$AccessibleJPanel(this);
        }
        return accessibleContext;
    }
    {
    }
}
