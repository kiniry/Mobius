package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.accessibility.*;
import java.io.Serializable;
import javax.swing.border.*;

public class JRootPane$RootLayout implements LayoutManager2, Serializable {
    /*synthetic*/ final JRootPane this$0;
    
    protected JRootPane$RootLayout(/*synthetic*/ final JRootPane this$0) {
        this.this$0 = this$0;
        
    }
    
    public Dimension preferredLayoutSize(Container parent) {
        Dimension rd;
        Dimension mbd;
        Insets i = this$0.getInsets();
        if (this$0.contentPane != null) {
            rd = this$0.contentPane.getPreferredSize();
        } else {
            rd = parent.getSize();
        }
        if (this$0.menuBar != null && this$0.menuBar.isVisible()) {
            mbd = this$0.menuBar.getPreferredSize();
        } else {
            mbd = new Dimension(0, 0);
        }
        return new Dimension(Math.max(rd.width, mbd.width) + i.left + i.right, rd.height + mbd.height + i.top + i.bottom);
    }
    
    public Dimension minimumLayoutSize(Container parent) {
        Dimension rd;
        Dimension mbd;
        Insets i = this$0.getInsets();
        if (this$0.contentPane != null) {
            rd = this$0.contentPane.getMinimumSize();
        } else {
            rd = parent.getSize();
        }
        if (this$0.menuBar != null && this$0.menuBar.isVisible()) {
            mbd = this$0.menuBar.getMinimumSize();
        } else {
            mbd = new Dimension(0, 0);
        }
        return new Dimension(Math.max(rd.width, mbd.width) + i.left + i.right, rd.height + mbd.height + i.top + i.bottom);
    }
    
    public Dimension maximumLayoutSize(Container target) {
        Dimension rd;
        Dimension mbd;
        Insets i = this$0.getInsets();
        if (this$0.menuBar != null && this$0.menuBar.isVisible()) {
            mbd = this$0.menuBar.getMaximumSize();
        } else {
            mbd = new Dimension(0, 0);
        }
        if (this$0.contentPane != null) {
            rd = this$0.contentPane.getMaximumSize();
        } else {
            rd = new Dimension(Integer.MAX_VALUE, Integer.MAX_VALUE - i.top - i.bottom - mbd.height - 1);
        }
        return new Dimension(Math.min(rd.width, mbd.width) + i.left + i.right, rd.height + mbd.height + i.top + i.bottom);
    }
    
    public void layoutContainer(Container parent) {
        Rectangle b = parent.getBounds();
        Insets i = this$0.getInsets();
        int contentY = 0;
        int w = b.width - i.right - i.left;
        int h = b.height - i.top - i.bottom;
        if (this$0.layeredPane != null) {
            this$0.layeredPane.setBounds(i.left, i.top, w, h);
        }
        if (this$0.glassPane != null) {
            this$0.glassPane.setBounds(i.left, i.top, w, h);
        }
        if (this$0.menuBar != null && this$0.menuBar.isVisible()) {
            Dimension mbd = this$0.menuBar.getPreferredSize();
            this$0.menuBar.setBounds(0, 0, w, mbd.height);
            contentY += mbd.height;
        }
        if (this$0.contentPane != null) {
            this$0.contentPane.setBounds(0, contentY, w, h - contentY);
        }
    }
    
    public void addLayoutComponent(String name, Component comp) {
    }
    
    public void removeLayoutComponent(Component comp) {
    }
    
    public void addLayoutComponent(Component comp, Object constraints) {
    }
    
    public float getLayoutAlignmentX(Container target) {
        return 0.0F;
    }
    
    public float getLayoutAlignmentY(Container target) {
        return 0.0F;
    }
    
    public void invalidateLayout(Container target) {
    }
}
