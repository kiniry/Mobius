package javax.swing;

import java.awt.Dimension;
import java.awt.event.*;
import java.beans.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JToolBar$Separator extends JSeparator {
    private Dimension separatorSize;
    
    public JToolBar$Separator() {
        this(null);
    }
    
    public JToolBar$Separator(Dimension size) {
        super(JSeparator.HORIZONTAL);
        setSeparatorSize(size);
    }
    
    public String getUIClassID() {
        return "ToolBarSeparatorUI";
    }
    
    public void setSeparatorSize(Dimension size) {
        if (size != null) {
            separatorSize = size;
        } else {
            super.updateUI();
        }
        this.invalidate();
    }
    
    public Dimension getSeparatorSize() {
        return separatorSize;
    }
    
    public Dimension getMinimumSize() {
        if (separatorSize != null) {
            return separatorSize.getSize();
        } else {
            return super.getMinimumSize();
        }
    }
    
    public Dimension getMaximumSize() {
        if (separatorSize != null) {
            return separatorSize.getSize();
        } else {
            return super.getMaximumSize();
        }
    }
    
    public Dimension getPreferredSize() {
        if (separatorSize != null) {
            return separatorSize.getSize();
        } else {
            return super.getPreferredSize();
        }
    }
}
