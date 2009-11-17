package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import java.awt.Component;
import java.awt.Insets;

class BasicBorders$RolloverMarginBorder extends EmptyBorder {
    
    public BasicBorders$RolloverMarginBorder() {
        super(3, 3, 3, 3);
    }
    
    public Insets getBorderInsets(Component c) {
        return getBorderInsets(c, new Insets(0, 0, 0, 0));
    }
    
    public Insets getBorderInsets(Component c, Insets insets) {
        Insets margin = null;
        if (c instanceof AbstractButton) {
            margin = ((AbstractButton)(AbstractButton)c).getMargin();
        }
        if (margin == null || margin instanceof UIResource) {
            insets.left = left;
            insets.top = top;
            insets.right = right;
            insets.bottom = bottom;
        } else {
            insets.left = margin.left;
            insets.top = margin.top;
            insets.right = margin.right;
            insets.bottom = margin.bottom;
        }
        return insets;
    }
}
