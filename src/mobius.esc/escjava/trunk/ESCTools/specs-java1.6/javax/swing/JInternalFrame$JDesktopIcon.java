package javax.swing;

import java.awt.*;
import java.awt.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.ObjectOutputStream;
import java.io.IOException;

public class JInternalFrame$JDesktopIcon extends JComponent implements Accessible {
    JInternalFrame internalFrame;
    
    public JInternalFrame$JDesktopIcon(JInternalFrame f) {
        
        setVisible(false);
        setInternalFrame(f);
        updateUI();
    }
    
    public DesktopIconUI getUI() {
        return (DesktopIconUI)(DesktopIconUI)ui;
    }
    
    public void setUI(DesktopIconUI ui) {
        super.setUI(ui);
    }
    
    public JInternalFrame getInternalFrame() {
        return internalFrame;
    }
    
    public void setInternalFrame(JInternalFrame f) {
        internalFrame = f;
    }
    
    public JDesktopPane getDesktopPane() {
        if (getInternalFrame() != null) return getInternalFrame().getDesktopPane();
        return null;
    }
    
    public void updateUI() {
        boolean hadUI = (ui != null);
        setUI((DesktopIconUI)(DesktopIconUI)UIManager.getUI(this));
        invalidate();
        Dimension r = getPreferredSize();
        setSize(r.width, r.height);
        if (internalFrame != null && internalFrame.getUI() != null) {
            SwingUtilities.updateComponentTreeUI(internalFrame);
        }
    }
    
    void updateUIWhenHidden() {
        setUI((DesktopIconUI)(DesktopIconUI)UIManager.getUI(this));
        Dimension r = getPreferredSize();
        setSize(r.width, r.height);
        invalidate();
        Component[] children = getComponents();
        if (children != null) {
            for (int i = 0; i < children.length; i++) {
                SwingUtilities.updateComponentTreeUI(children[i]);
            }
        }
    }
    
    public String getUIClassID() {
        return "DesktopIconUI";
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        if (getUIClassID().equals("DesktopIconUI")) {
            byte count = JComponent.getWriteObjCounter(this);
            JComponent.setWriteObjCounter(this, --count);
            if (count == 0 && ui != null) {
                ui.installUI(this);
            }
        }
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JInternalFrame$JDesktopIcon$AccessibleJDesktopIcon(this);
        }
        return accessibleContext;
    }
    {
    }
}
