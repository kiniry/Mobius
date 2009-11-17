package javax.swing;

import java.awt.*;
import java.awt.event.*;
import javax.accessibility.*;

public class Box extends JComponent implements Accessible {
    
    public Box(int axis) {
        
        super.setLayout(new BoxLayout(this, axis));
    }
    
    public static Box createHorizontalBox() {
        return new Box(BoxLayout.X_AXIS);
    }
    
    public static Box createVerticalBox() {
        return new Box(BoxLayout.Y_AXIS);
    }
    
    public static Component createRigidArea(Dimension d) {
        return new Box$Filler(d, d, d);
    }
    
    public static Component createHorizontalStrut(int width) {
        return new Box$Filler(new Dimension(width, 0), new Dimension(width, 0), new Dimension(width, Short.MAX_VALUE));
    }
    
    public static Component createVerticalStrut(int height) {
        return new Box$Filler(new Dimension(0, height), new Dimension(0, height), new Dimension(Short.MAX_VALUE, height));
    }
    
    public static Component createGlue() {
        return new Box$Filler(new Dimension(0, 0), new Dimension(0, 0), new Dimension(Short.MAX_VALUE, Short.MAX_VALUE));
    }
    
    public static Component createHorizontalGlue() {
        return new Box$Filler(new Dimension(0, 0), new Dimension(0, 0), new Dimension(Short.MAX_VALUE, 0));
    }
    
    public static Component createVerticalGlue() {
        return new Box$Filler(new Dimension(0, 0), new Dimension(0, 0), new Dimension(0, Short.MAX_VALUE));
    }
    
    public void setLayout(LayoutManager l) {
        throw new AWTError("Illegal request");
    }
    {
    }
    protected AccessibleContext accessibleContext = null;
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new Box$AccessibleBox(this);
        }
        return accessibleContext;
    }
    {
    }
}
