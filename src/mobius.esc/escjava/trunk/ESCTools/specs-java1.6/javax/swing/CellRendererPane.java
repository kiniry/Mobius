package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import javax.accessibility.*;

public class CellRendererPane extends Container implements Accessible {
    
    public CellRendererPane() {
        
        setLayout(null);
        setVisible(false);
    }
    
    public void invalidate() {
    }
    
    public void paint(Graphics g) {
    }
    
    public void update(Graphics g) {
    }
    
    protected void addImpl(Component x, Object constraints, int index) {
        if (x.getParent() == this) {
            return;
        } else {
            super.addImpl(x, constraints, index);
        }
    }
    
    public void paintComponent(Graphics g, Component c, Container p, int x, int y, int w, int h, boolean shouldValidate) {
        if (c == null) {
            if (p != null) {
                Color oldColor = g.getColor();
                g.setColor(p.getBackground());
                g.fillRect(x, y, w, h);
                g.setColor(oldColor);
            }
            return;
        }
        if (c.getParent() != this) {
            this.add(c);
        }
        c.setBounds(x, y, w, h);
        if (shouldValidate) {
            c.validate();
        }
        boolean wasDoubleBuffered = false;
        if ((c instanceof JComponent) && ((JComponent)(JComponent)c).isDoubleBuffered()) {
            wasDoubleBuffered = true;
            ((JComponent)(JComponent)c).setDoubleBuffered(false);
        }
        Graphics cg = g.create(x, y, w, h);
        try {
            c.paint(cg);
        } finally {
            cg.dispose();
        }
        if (wasDoubleBuffered && (c instanceof JComponent)) {
            ((JComponent)(JComponent)c).setDoubleBuffered(true);
        }
        c.setBounds(-w, -h, 0, 0);
    }
    
    public void paintComponent(Graphics g, Component c, Container p, int x, int y, int w, int h) {
        paintComponent(g, c, p, x, y, w, h, false);
    }
    
    public void paintComponent(Graphics g, Component c, Container p, Rectangle r) {
        paintComponent(g, c, p, r.x, r.y, r.width, r.height);
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        removeAll();
        s.defaultWriteObject();
    }
    protected AccessibleContext accessibleContext = null;
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new CellRendererPane$AccessibleCellRendererPane(this);
        }
        return accessibleContext;
    }
    {
    }
}
