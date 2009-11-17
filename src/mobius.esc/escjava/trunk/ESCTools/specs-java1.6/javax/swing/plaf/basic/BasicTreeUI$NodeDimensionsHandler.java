package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.dnd.*;
import java.beans.*;
import java.io.*;
import javax.swing.tree.*;

public class BasicTreeUI$NodeDimensionsHandler extends AbstractLayoutCache$NodeDimensions {
    /*synthetic*/ final BasicTreeUI this$0;
    
    public BasicTreeUI$NodeDimensionsHandler(/*synthetic*/ final BasicTreeUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public Rectangle getNodeDimensions(Object value, int row, int depth, boolean expanded, Rectangle size) {
        if (this$0.editingComponent != null && this$0.editingRow == row) {
            Dimension prefSize = this$0.editingComponent.getPreferredSize();
            int rh = this$0.getRowHeight();
            if (rh > 0 && rh != prefSize.height) prefSize.height = rh;
            if (size != null) {
                size.x = getRowX(row, depth);
                size.width = prefSize.width;
                size.height = prefSize.height;
            } else {
                size = new Rectangle(getRowX(row, depth), 0, prefSize.width, prefSize.height);
            }
            if (!BasicTreeUI.access$300(this$0)) {
                size.x = BasicTreeUI.access$400(this$0) - size.width - size.x - 2;
            }
            return size;
        }
        if (this$0.currentCellRenderer != null) {
            Component aComponent;
            aComponent = this$0.currentCellRenderer.getTreeCellRendererComponent(this$0.tree, value, this$0.tree.isRowSelected(row), expanded, this$0.treeModel.isLeaf(value), row, false);
            if (this$0.tree != null) {
                this$0.rendererPane.add(aComponent);
                aComponent.validate();
            }
            Dimension prefSize = aComponent.getPreferredSize();
            if (size != null) {
                size.x = getRowX(row, depth);
                size.width = prefSize.width;
                size.height = prefSize.height;
            } else {
                size = new Rectangle(getRowX(row, depth), 0, prefSize.width, prefSize.height);
            }
            if (!BasicTreeUI.access$300(this$0)) {
                size.x = BasicTreeUI.access$400(this$0) - size.width - size.x - 2;
            }
            return size;
        }
        return null;
    }
    
    protected int getRowX(int row, int depth) {
        return this$0.getRowX(row, depth);
    }
}
