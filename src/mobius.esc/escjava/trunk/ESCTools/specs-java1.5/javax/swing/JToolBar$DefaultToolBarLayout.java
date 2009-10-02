package javax.swing;

import java.awt.Component;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.LayoutManager;
import java.awt.LayoutManager2;
import java.awt.event.*;
import java.beans.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.Serializable;

class JToolBar$DefaultToolBarLayout implements LayoutManager2, Serializable, PropertyChangeListener, UIResource {
    /*synthetic*/ final JToolBar this$0;
    LayoutManager lm;
    
    JToolBar$DefaultToolBarLayout(/*synthetic*/ final JToolBar this$0, int orientation) {
        this.this$0 = this$0;
        
        if (orientation == JToolBar.VERTICAL) {
            lm = new BoxLayout(this$0, BoxLayout.PAGE_AXIS);
        } else {
            lm = new BoxLayout(this$0, BoxLayout.LINE_AXIS);
        }
    }
    
    public void addLayoutComponent(String name, Component comp) {
    }
    
    public void addLayoutComponent(Component comp, Object constraints) {
    }
    
    public void removeLayoutComponent(Component comp) {
    }
    
    public Dimension preferredLayoutSize(Container target) {
        return lm.preferredLayoutSize(target);
    }
    
    public Dimension minimumLayoutSize(Container target) {
        return lm.minimumLayoutSize(target);
    }
    
    public Dimension maximumLayoutSize(Container target) {
        if (lm instanceof LayoutManager2) {
            return ((LayoutManager2)(LayoutManager2)lm).maximumLayoutSize(target);
        } else {
            return new Dimension(Short.MAX_VALUE, Short.MAX_VALUE);
        }
    }
    
    public void layoutContainer(Container target) {
        lm.layoutContainer(target);
    }
    
    public float getLayoutAlignmentX(Container target) {
        if (lm instanceof LayoutManager2) {
            return ((LayoutManager2)(LayoutManager2)lm).getLayoutAlignmentX(target);
        } else {
            return 0.5F;
        }
    }
    
    public float getLayoutAlignmentY(Container target) {
        if (lm instanceof LayoutManager2) {
            return ((LayoutManager2)(LayoutManager2)lm).getLayoutAlignmentY(target);
        } else {
            return 0.5F;
        }
    }
    
    public void invalidateLayout(Container target) {
        if (lm instanceof LayoutManager2) {
            ((LayoutManager2)(LayoutManager2)lm).invalidateLayout(target);
        }
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        String name = e.getPropertyName();
        if (name.equals("orientation")) {
            int o = ((Integer)(Integer)e.getNewValue()).intValue();
            if (o == JToolBar.VERTICAL) lm = new BoxLayout(this$0, BoxLayout.PAGE_AXIS); else {
                lm = new BoxLayout(this$0, BoxLayout.LINE_AXIS);
            }
        }
    }
}
