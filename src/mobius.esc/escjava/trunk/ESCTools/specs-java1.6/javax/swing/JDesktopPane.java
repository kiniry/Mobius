package javax.swing;

import java.util.Vector;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.ObjectOutputStream;
import java.io.IOException;

public class JDesktopPane extends JLayeredPane implements Accessible {
    private static final String uiClassID = "DesktopPaneUI";
    transient DesktopManager desktopManager;
    private transient JInternalFrame selectedFrame = null;
    public static final int LIVE_DRAG_MODE = 0;
    public static final int OUTLINE_DRAG_MODE = 1;
    private int dragMode = LIVE_DRAG_MODE;
    private boolean dragModeSet = false;
    
    public JDesktopPane() {
        
        setFocusCycleRoot(true);
        setFocusTraversalPolicy(new JDesktopPane$1(this));
        updateUI();
    }
    
    public DesktopPaneUI getUI() {
        return (DesktopPaneUI)(DesktopPaneUI)ui;
    }
    
    public void setUI(DesktopPaneUI ui) {
        super.setUI(ui);
    }
    
    public void setDragMode(int dragMode) {
        int oldDragMode = this.dragMode;
        this.dragMode = dragMode;
        firePropertyChange("dragMode", oldDragMode, this.dragMode);
        dragModeSet = true;
    }
    
    public int getDragMode() {
        return dragMode;
    }
    
    public DesktopManager getDesktopManager() {
        return desktopManager;
    }
    
    public void setDesktopManager(DesktopManager d) {
        DesktopManager oldValue = desktopManager;
        desktopManager = d;
        firePropertyChange("desktopManager", oldValue, desktopManager);
    }
    
    public void updateUI() {
        setUI((DesktopPaneUI)(DesktopPaneUI)UIManager.getUI(this));
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    public JInternalFrame[] getAllFrames() {
        int i;
        int count;
        JInternalFrame[] results;
        Vector vResults = new Vector(10);
        Object next;
        Object tmp;
        count = getComponentCount();
        for (i = 0; i < count; i++) {
            next = getComponent(i);
            if (next instanceof JInternalFrame) vResults.addElement(next); else if (next instanceof JInternalFrame$JDesktopIcon) {
                tmp = ((JInternalFrame$JDesktopIcon)(JInternalFrame$JDesktopIcon)next).getInternalFrame();
                if (tmp != null) vResults.addElement(tmp);
            }
        }
        results = new JInternalFrame[vResults.size()];
        vResults.copyInto(results);
        return results;
    }
    
    public JInternalFrame getSelectedFrame() {
        return selectedFrame;
    }
    
    public void setSelectedFrame(JInternalFrame f) {
        selectedFrame = f;
    }
    
    public JInternalFrame[] getAllFramesInLayer(int layer) {
        int i;
        int count;
        JInternalFrame[] results;
        Vector vResults = new Vector(10);
        Object next;
        Object tmp;
        count = getComponentCount();
        for (i = 0; i < count; i++) {
            next = getComponent(i);
            if (next instanceof JInternalFrame) {
                if (((JInternalFrame)(JInternalFrame)next).getLayer() == layer) vResults.addElement(next);
            } else if (next instanceof JInternalFrame$JDesktopIcon) {
                tmp = ((JInternalFrame$JDesktopIcon)(JInternalFrame$JDesktopIcon)next).getInternalFrame();
                if (tmp != null && ((JInternalFrame)(JInternalFrame)tmp).getLayer() == layer) vResults.addElement(tmp);
            }
        }
        results = new JInternalFrame[vResults.size()];
        vResults.copyInto(results);
        return results;
    }
    
    public boolean isOpaque() {
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
    
    void setUIProperty(String propertyName, Object value) {
        if (propertyName == "dragMode") {
            if (!dragModeSet) {
                setDragMode(((Integer)(Integer)value).intValue());
                dragModeSet = false;
            }
        } else {
            super.setUIProperty(propertyName, value);
        }
    }
    
    protected String paramString() {
        String desktopManagerString = (desktopManager != null ? desktopManager.toString() : "");
        return super.paramString() + ",desktopManager=" + desktopManagerString;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JDesktopPane$AccessibleJDesktopPane(this);
        }
        return accessibleContext;
    }
    {
    }
}
