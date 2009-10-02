package javax.swing.tree;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import javax.swing.plaf.FontUIResource;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.io.*;

public class DefaultTreeCellEditor$DefaultTextField extends JTextField {
    /*synthetic*/ final DefaultTreeCellEditor this$0;
    protected Border border;
    
    public DefaultTreeCellEditor$DefaultTextField(/*synthetic*/ final DefaultTreeCellEditor this$0, Border border) {
        this.this$0 = this$0;
        
        setBorder(border);
    }
    
    public void setBorder(Border border) {
        super.setBorder(border);
        this.border = border;
    }
    
    public Border getBorder() {
        return border;
    }
    
    public Font getFont() {
        Font font = super.getFont();
        if (font instanceof FontUIResource) {
            Container parent = getParent();
            if (parent != null && parent.getFont() != null) font = parent.getFont();
        }
        return font;
    }
    
    public Dimension getPreferredSize() {
        Dimension size = super.getPreferredSize();
        if (this$0.renderer != null && this$0.getFont() == null) {
            Dimension rSize = this$0.renderer.getPreferredSize();
            size.height = rSize.height;
        }
        return size;
    }
}
