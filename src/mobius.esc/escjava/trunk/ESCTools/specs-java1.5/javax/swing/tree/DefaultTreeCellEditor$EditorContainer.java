package javax.swing.tree;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.io.*;

public class DefaultTreeCellEditor$EditorContainer extends Container {
    /*synthetic*/ final DefaultTreeCellEditor this$0;
    
    public DefaultTreeCellEditor$EditorContainer(/*synthetic*/ final DefaultTreeCellEditor this$0) {
        this.this$0 = this$0;
        
        setLayout(null);
    }
    
    public void EditorContainer() {
        setLayout(null);
    }
    
    public void paint(Graphics g) {
        Dimension size = getSize();
        if (this$0.editingIcon != null) {
            int yLoc = Math.max(0, (getSize().height - this$0.editingIcon.getIconHeight()) / 2);
            this$0.editingIcon.paintIcon(this, g, 0, yLoc);
        }
        Color background = this$0.getBorderSelectionColor();
        if (background != null) {
            g.setColor(background);
            g.drawRect(0, 0, size.width - 1, size.height - 1);
        }
        super.paint(g);
    }
    
    public void doLayout() {
        if (this$0.editingComponent != null) {
            Dimension cSize = getSize();
            this$0.editingComponent.getPreferredSize();
            this$0.editingComponent.setLocation(this$0.offset, 0);
            this$0.editingComponent.setBounds(this$0.offset, 0, cSize.width - this$0.offset, cSize.height);
        }
    }
    
    public Dimension getPreferredSize() {
        if (this$0.editingComponent != null) {
            Dimension pSize = this$0.editingComponent.getPreferredSize();
            pSize.width += this$0.offset + 5;
            Dimension rSize = (this$0.renderer != null) ? this$0.renderer.getPreferredSize() : null;
            if (rSize != null) pSize.height = Math.max(pSize.height, rSize.height);
            if (this$0.editingIcon != null) pSize.height = Math.max(pSize.height, this$0.editingIcon.getIconHeight());
            pSize.width = Math.max(pSize.width, 100);
            return pSize;
        }
        return new Dimension(0, 0);
    }
}
