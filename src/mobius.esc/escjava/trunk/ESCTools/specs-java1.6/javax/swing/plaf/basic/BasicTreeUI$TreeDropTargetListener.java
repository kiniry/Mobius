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

class BasicTreeUI$TreeDropTargetListener extends BasicDropTargetListener {
    
    BasicTreeUI$TreeDropTargetListener() {
        
    }
    
    protected void saveComponentState(JComponent comp) {
        JTree tree = (JTree)(JTree)comp;
        selectedIndices = tree.getSelectionRows();
    }
    
    protected void restoreComponentState(JComponent comp) {
        JTree tree = (JTree)(JTree)comp;
        tree.setSelectionRows(selectedIndices);
    }
    
    protected void updateInsertionLocation(JComponent comp, Point p) {
        JTree tree = (JTree)(JTree)comp;
        BasicTreeUI ui = (BasicTreeUI)(BasicTreeUI)tree.getUI();
        TreePath path = ui.getClosestPathForLocation(tree, p.x, p.y);
        if (path != null) {
            tree.setSelectionPath(path);
        }
    }
    private int[] selectedIndices;
}
