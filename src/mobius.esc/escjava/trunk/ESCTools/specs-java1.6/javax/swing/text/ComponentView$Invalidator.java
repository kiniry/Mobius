package javax.swing.text;

import java.awt.*;
import javax.swing.event.*;

class ComponentView$Invalidator extends Container {
    /*synthetic*/ final ComponentView this$0;
    
    ComponentView$Invalidator(/*synthetic*/ final ComponentView this$0, Component child) {
        this.this$0 = this$0;
        
        setLayout(null);
        add(child);
        cacheChildSizes();
    }
    
    public void invalidate() {
        super.invalidate();
        if (getParent() != null) {
            this$0.preferenceChanged(null, true, true);
        }
    }
    
    public void doLayout() {
        cacheChildSizes();
    }
    
    public void setBounds(int x, int y, int w, int h) {
        super.setBounds(x, y, w, h);
        if (getComponentCount() > 0) {
            getComponent(0).setSize(w, h);
        }
        cacheChildSizes();
    }
    
    public void validateIfNecessary() {
        if (!isValid()) {
            validate();
        }
    }
    
    private void cacheChildSizes() {
        if (getComponentCount() > 0) {
            Component child = getComponent(0);
            min = child.getMinimumSize();
            pref = child.getPreferredSize();
            max = child.getMaximumSize();
            yalign = child.getAlignmentY();
            xalign = child.getAlignmentX();
        } else {
            min = pref = max = new Dimension(0, 0);
        }
    }
    
    public void setVisible(boolean b) {
        super.setVisible(b);
        if (getComponentCount() > 0) {
            getComponent(0).setVisible(b);
        }
    }
    
    public boolean isShowing() {
        return true;
    }
    
    public Dimension getMinimumSize() {
        validateIfNecessary();
        return min;
    }
    
    public Dimension getPreferredSize() {
        validateIfNecessary();
        return pref;
    }
    
    public Dimension getMaximumSize() {
        validateIfNecessary();
        return max;
    }
    
    public float getAlignmentX() {
        validateIfNecessary();
        return xalign;
    }
    
    public float getAlignmentY() {
        validateIfNecessary();
        return yalign;
    }
    
    public java.util.Set getFocusTraversalKeys(int id) {
        return KeyboardFocusManager.getCurrentKeyboardFocusManager().getDefaultFocusTraversalKeys(id);
    }
    Dimension min;
    Dimension pref;
    Dimension max;
    float yalign;
    float xalign;
}
