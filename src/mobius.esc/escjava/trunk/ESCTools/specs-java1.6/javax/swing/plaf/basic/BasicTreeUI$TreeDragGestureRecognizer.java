package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.dnd.*;
import java.beans.*;
import java.io.*;
import javax.swing.plaf.TreeUI;
import javax.swing.tree.*;

class BasicTreeUI$TreeDragGestureRecognizer extends BasicDragGestureRecognizer {
    
    BasicTreeUI$TreeDragGestureRecognizer() {
        
    }
    
    protected boolean isDragPossible(MouseEvent e) {
        if (super.isDragPossible(e)) {
            JTree tree = (JTree)(JTree)this.getComponent(e);
            if (tree.getDragEnabled()) {
                TreeUI ui = tree.getUI();
                TreePath path = ui.getClosestPathForLocation(tree, e.getX(), e.getY());
                if ((path != null) && tree.isPathSelected(path)) {
                    return true;
                }
            }
        }
        return false;
    }
}
