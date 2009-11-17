package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.dnd.*;
import java.beans.*;
import java.io.*;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import javax.swing.plaf.UIResource;
import javax.swing.tree.*;

class BasicTreeUI$TreeTransferHandler extends TransferHandler implements UIResource, Comparator {
    
    BasicTreeUI$TreeTransferHandler() {
        
    }
    private JTree tree;
    
    protected Transferable createTransferable(JComponent c) {
        if (c instanceof JTree) {
            tree = (JTree)(JTree)c;
            TreePath[] paths = tree.getSelectionPaths();
            if (paths == null || paths.length == 0) {
                return null;
            }
            StringBuffer plainBuf = new StringBuffer();
            StringBuffer htmlBuf = new StringBuffer();
            htmlBuf.append("<html>\n<body>\n<ul>\n");
            TreeModel model = tree.getModel();
            TreePath lastPath = null;
            TreePath[] displayPaths = getDisplayOrderPaths(paths);
            for (int i = 0; i < displayPaths.length; i++) {
                TreePath path = displayPaths[i];
                Object node = path.getLastPathComponent();
                boolean leaf = model.isLeaf(node);
                String label = getDisplayString(path, true, leaf);
                plainBuf.append(label + "\n");
                htmlBuf.append("  <li>" + label + "\n");
            }
            plainBuf.deleteCharAt(plainBuf.length() - 1);
            htmlBuf.append("</ul>\n</body>\n</html>");
            tree = null;
            return new BasicTransferable(plainBuf.toString(), htmlBuf.toString());
        }
        return null;
    }
    
    public int compare(Object o1, Object o2) {
        int row1 = tree.getRowForPath((TreePath)(TreePath)o1);
        int row2 = tree.getRowForPath((TreePath)(TreePath)o2);
        return row1 - row2;
    }
    
    String getDisplayString(TreePath path, boolean selected, boolean leaf) {
        int row = tree.getRowForPath(path);
        boolean hasFocus = tree.getLeadSelectionRow() == row;
        Object node = path.getLastPathComponent();
        return tree.convertValueToText(node, selected, tree.isExpanded(row), leaf, row, hasFocus);
    }
    
    TreePath[] getDisplayOrderPaths(TreePath[] paths) {
        ArrayList selOrder = new ArrayList();
        for (int i = 0; i < paths.length; i++) {
            selOrder.add(paths[i]);
        }
        Collections.sort(selOrder, this);
        int n = selOrder.size();
        TreePath[] displayPaths = new TreePath[n];
        for (int i = 0; i < n; i++) {
            displayPaths[i] = (TreePath)(TreePath)selOrder.get(i);
        }
        return displayPaths;
    }
    
    public int getSourceActions(JComponent c) {
        return COPY;
    }
}
