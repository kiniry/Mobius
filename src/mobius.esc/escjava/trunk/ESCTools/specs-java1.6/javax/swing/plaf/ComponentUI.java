package javax.swing.plaf;

import javax.swing.JComponent;
import javax.swing.SwingUtilities;
import javax.accessibility.Accessible;
import java.awt.Dimension;
import java.awt.Graphics;

public abstract class ComponentUI {
    
    public ComponentUI() {
        
    }
    
    public void installUI(JComponent c) {
    }
    
    public void uninstallUI(JComponent c) {
    }
    
    public void paint(Graphics g, JComponent c) {
    }
    
    public void update(Graphics g, JComponent c) {
        if (c.isOpaque()) {
            g.setColor(c.getBackground());
            g.fillRect(0, 0, c.getWidth(), c.getHeight());
        }
        paint(g, c);
    }
    
    public Dimension getPreferredSize(JComponent c) {
        return null;
    }
    
    public Dimension getMinimumSize(JComponent c) {
        return getPreferredSize(c);
    }
    
    public Dimension getMaximumSize(JComponent c) {
        return getPreferredSize(c);
    }
    
    public boolean contains(JComponent c, int x, int y) {
        return c.inside(x, y);
    }
    
    public static ComponentUI createUI(JComponent c) {
        throw new Error("ComponentUI.createUI not implemented.");
    }
    
    public int getAccessibleChildrenCount(JComponent c) {
        return SwingUtilities.getAccessibleChildrenCount(c);
    }
    
    public Accessible getAccessibleChild(JComponent c, int i) {
        return SwingUtilities.getAccessibleChild(c, i);
    }
}
