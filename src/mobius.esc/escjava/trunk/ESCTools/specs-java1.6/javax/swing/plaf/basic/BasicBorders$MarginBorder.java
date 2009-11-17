package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import javax.swing.text.JTextComponent;
import java.awt.Component;
import java.awt.Insets;

public class BasicBorders$MarginBorder extends AbstractBorder implements UIResource {
    
    public BasicBorders$MarginBorder() {
        
    }
    
    public Insets getBorderInsets(Component c) {
        return getBorderInsets(c, new Insets(0, 0, 0, 0));
    }
    
    public Insets getBorderInsets(Component c, Insets insets) {
        Insets margin = null;
        if (c instanceof AbstractButton) {
            AbstractButton b = (AbstractButton)(AbstractButton)c;
            margin = b.getMargin();
        } else if (c instanceof JToolBar) {
            JToolBar t = (JToolBar)(JToolBar)c;
            margin = t.getMargin();
        } else if (c instanceof JTextComponent) {
            JTextComponent t = (JTextComponent)(JTextComponent)c;
            margin = t.getMargin();
        }
        insets.top = margin != null ? margin.top : 0;
        insets.left = margin != null ? margin.left : 0;
        insets.bottom = margin != null ? margin.bottom : 0;
        insets.right = margin != null ? margin.right : 0;
        return insets;
    }
}
