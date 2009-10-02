package javax.swing;

import java.awt.*;
import java.awt.event.*;
import javax.accessibility.*;

public class Box$Filler extends JComponent implements Accessible {
    
    public Box$Filler(Dimension min, Dimension pref, Dimension max) {
        
        reqMin = min;
        reqPref = pref;
        reqMax = max;
    }
    
    public void changeShape(Dimension min, Dimension pref, Dimension max) {
        reqMin = min;
        reqPref = pref;
        reqMax = max;
        invalidate();
    }
    
    public Dimension getMinimumSize() {
        return reqMin;
    }
    
    public Dimension getPreferredSize() {
        return reqPref;
    }
    
    public Dimension getMaximumSize() {
        return reqMax;
    }
    private Dimension reqMin;
    private Dimension reqPref;
    private Dimension reqMax;
    protected AccessibleContext accessibleContext = null;
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new Box$Filler$AccessibleBoxFiller(this);
        }
        return accessibleContext;
    }
    {
    }
}
