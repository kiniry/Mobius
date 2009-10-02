package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.io.*;
import java.util.*;
import javax.swing.event.*;
import javax.swing.tree.*;
import javax.accessibility.*;

public class JTree$TreeModelHandler implements TreeModelListener {
    /*synthetic*/ final JTree this$0;
    
    protected JTree$TreeModelHandler(/*synthetic*/ final JTree this$0) {
        this.this$0 = this$0;
        
    }
    
    public void treeNodesChanged(TreeModelEvent e) {
    }
    
    public void treeNodesInserted(TreeModelEvent e) {
    }
    
    public void treeStructureChanged(TreeModelEvent e) {
        if (e == null) return;
        TreePath parent = e.getTreePath();
        if (parent == null) return;
        if (parent.getPathCount() == 1) {
            this$0.clearToggledPaths();
            if (this$0.treeModel.getRoot() != null && !this$0.treeModel.isLeaf(this$0.treeModel.getRoot())) {
                JTree.access$000(this$0).put(parent, Boolean.TRUE);
            }
        } else if (JTree.access$000(this$0).get(parent) != null) {
            Vector toRemove = new Vector(1);
            boolean isExpanded = this$0.isExpanded(parent);
            toRemove.addElement(parent);
            this$0.removeDescendantToggledPaths(toRemove.elements());
            if (isExpanded) {
                TreeModel model = this$0.getModel();
                if (model == null || model.isLeaf(parent.getLastPathComponent())) this$0.collapsePath(parent); else JTree.access$000(this$0).put(parent, Boolean.TRUE);
            }
        }
        this$0.removeDescendantSelectedPaths(parent, false);
    }
    
    public void treeNodesRemoved(TreeModelEvent e) {
        if (e == null) return;
        TreePath parent = e.getTreePath();
        Object[] children = e.getChildren();
        if (children == null) return;
        TreePath rPath;
        Vector toRemove = new Vector(Math.max(1, children.length));
        for (int counter = children.length - 1; counter >= 0; counter--) {
            rPath = parent.pathByAddingChild(children[counter]);
            if (JTree.access$000(this$0).get(rPath) != null) toRemove.addElement(rPath);
        }
        if (toRemove.size() > 0) this$0.removeDescendantToggledPaths(toRemove.elements());
        TreeModel model = this$0.getModel();
        if (model == null || model.isLeaf(parent.getLastPathComponent())) JTree.access$000(this$0).remove(parent);
        this$0.removeDescendantSelectedPaths(e);
    }
}
