package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.io.*;
import java.util.*;
import javax.swing.event.*;
import javax.swing.plaf.TreeUI;
import javax.swing.tree.*;
import javax.accessibility.*;

public class JTree$AccessibleJTree extends JComponent$AccessibleJComponent implements AccessibleSelection, TreeSelectionListener, TreeModelListener, TreeExpansionListener {
    /*synthetic*/ final JTree this$0;
    TreePath leadSelectionPath;
    Accessible leadSelectionAccessible;
    
    public JTree$AccessibleJTree(/*synthetic*/ final JTree this$0) {
        this.this$0 = this$0;
        super(this$0);
        TreeModel model = this$0.getModel();
        if (model != null) {
            model.addTreeModelListener(this);
        }
        this$0.addTreeExpansionListener(this);
        this$0.addTreeSelectionListener(this);
        leadSelectionPath = this$0.getLeadSelectionPath();
        leadSelectionAccessible = (leadSelectionPath != null) ? new JTree$AccessibleJTree$AccessibleJTreeNode(this, this$0, leadSelectionPath, this$0) : null;
    }
    
    public void valueChanged(TreeSelectionEvent e) {
        TreePath oldLeadSelectionPath = e.getOldLeadSelectionPath();
        leadSelectionPath = e.getNewLeadSelectionPath();
        if (oldLeadSelectionPath != leadSelectionPath) {
            Accessible oldLSA = leadSelectionAccessible;
            leadSelectionAccessible = (leadSelectionPath != null) ? new JTree$AccessibleJTree$AccessibleJTreeNode(this, this$0, leadSelectionPath, null) : null;
            firePropertyChange(AccessibleContext.ACCESSIBLE_ACTIVE_DESCENDANT_PROPERTY, oldLSA, leadSelectionAccessible);
        }
        firePropertyChange(AccessibleContext.ACCESSIBLE_SELECTION_PROPERTY, Boolean.valueOf(false), Boolean.valueOf(true));
    }
    
    public void fireVisibleDataPropertyChange() {
        firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, Boolean.valueOf(false), Boolean.valueOf(true));
    }
    
    public void treeNodesChanged(TreeModelEvent e) {
        fireVisibleDataPropertyChange();
    }
    
    public void treeNodesInserted(TreeModelEvent e) {
        fireVisibleDataPropertyChange();
    }
    
    public void treeNodesRemoved(TreeModelEvent e) {
        fireVisibleDataPropertyChange();
    }
    
    public void treeStructureChanged(TreeModelEvent e) {
        fireVisibleDataPropertyChange();
    }
    
    public void treeCollapsed(TreeExpansionEvent e) {
        fireVisibleDataPropertyChange();
        TreePath path = e.getPath();
        if (path != null) {
            JTree$AccessibleJTree$AccessibleJTreeNode node = new JTree$AccessibleJTree$AccessibleJTreeNode(this, this$0, path, null);
            PropertyChangeEvent pce = new PropertyChangeEvent(node, AccessibleContext.ACCESSIBLE_STATE_PROPERTY, AccessibleState.EXPANDED, AccessibleState.COLLAPSED);
            firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, pce);
        }
    }
    
    public void treeExpanded(TreeExpansionEvent e) {
        fireVisibleDataPropertyChange();
        TreePath path = e.getPath();
        if (path != null) {
            JTree$AccessibleJTree$AccessibleJTreeNode node = new JTree$AccessibleJTree$AccessibleJTreeNode(this, this$0, path, null);
            PropertyChangeEvent pce = new PropertyChangeEvent(node, AccessibleContext.ACCESSIBLE_STATE_PROPERTY, AccessibleState.COLLAPSED, AccessibleState.EXPANDED);
            firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, pce);
        }
    }
    
    private AccessibleContext getCurrentAccessibleContext() {
        Component c = getCurrentComponent();
        if (c instanceof Accessible) {
            return (((Accessible)(Accessible)c).getAccessibleContext());
        } else {
            return null;
        }
    }
    
    private Component getCurrentComponent() {
        TreeModel model = this$0.getModel();
        if (model == null) {
            return null;
        }
        TreePath path = new TreePath(model.getRoot());
        if (this$0.isVisible(path)) {
            TreeCellRenderer r = this$0.getCellRenderer();
            TreeUI ui = this$0.getUI();
            if (ui != null) {
                int row = ui.getRowForPath(this$0, path);
                int lsr = this$0.getLeadSelectionRow();
                boolean hasFocus = this$0.isFocusOwner() && (lsr == row);
                boolean selected = this$0.isPathSelected(path);
                boolean expanded = this$0.isExpanded(path);
                return r.getTreeCellRendererComponent(this$0, model.getRoot(), selected, expanded, model.isLeaf(model.getRoot()), row, hasFocus);
            }
        }
        return null;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.TREE;
    }
    
    public Accessible getAccessibleAt(Point p) {
        TreePath path = this$0.getClosestPathForLocation(p.x, p.y);
        if (path != null) {
            return new JTree$AccessibleJTree$AccessibleJTreeNode(this, this$0, path, null);
        } else {
            return null;
        }
    }
    
    public int getAccessibleChildrenCount() {
        TreeModel model = this$0.getModel();
        if (model != null) {
            return 1;
        } else {
            return 0;
        }
    }
    
    public Accessible getAccessibleChild(int i) {
        TreeModel model = this$0.getModel();
        if (model != null) {
            if (i != 0) {
                return null;
            } else {
                Object[] objPath = {model.getRoot()};
                TreePath path = new TreePath(objPath);
                return new JTree$AccessibleJTree$AccessibleJTreeNode(this, this$0, path, this$0);
            }
        }
        return null;
    }
    
    public int getAccessibleIndexInParent() {
        return super.getAccessibleIndexInParent();
    }
    
    public AccessibleSelection getAccessibleSelection() {
        return this;
    }
    
    public int getAccessibleSelectionCount() {
        Object[] rootPath = new Object[1];
        rootPath[0] = this$0.treeModel.getRoot();
        TreePath childPath = new TreePath(rootPath);
        if (this$0.isPathSelected(childPath)) {
            return 1;
        } else {
            return 0;
        }
    }
    
    public Accessible getAccessibleSelection(int i) {
        if (i == 0) {
            Object[] rootPath = new Object[1];
            rootPath[0] = this$0.treeModel.getRoot();
            TreePath childPath = new TreePath(rootPath);
            if (this$0.isPathSelected(childPath)) {
                return new JTree$AccessibleJTree$AccessibleJTreeNode(this, this$0, childPath, this$0);
            }
        }
        return null;
    }
    
    public boolean isAccessibleChildSelected(int i) {
        if (i == 0) {
            Object[] rootPath = new Object[1];
            rootPath[0] = this$0.treeModel.getRoot();
            TreePath childPath = new TreePath(rootPath);
            return this$0.isPathSelected(childPath);
        } else {
            return false;
        }
    }
    
    public void addAccessibleSelection(int i) {
        TreeModel model = this$0.getModel();
        if (model != null) {
            if (i == 0) {
                Object[] objPath = {model.getRoot()};
                TreePath path = new TreePath(objPath);
                this$0.addSelectionPath(path);
            }
        }
    }
    
    public void removeAccessibleSelection(int i) {
        TreeModel model = this$0.getModel();
        if (model != null) {
            if (i == 0) {
                Object[] objPath = {model.getRoot()};
                TreePath path = new TreePath(objPath);
                this$0.removeSelectionPath(path);
            }
        }
    }
    
    public void clearAccessibleSelection() {
        int childCount = getAccessibleChildrenCount();
        for (int i = 0; i < childCount; i++) {
            removeAccessibleSelection(i);
        }
    }
    
    public void selectAllAccessibleSelection() {
        TreeModel model = this$0.getModel();
        if (model != null) {
            Object[] objPath = {model.getRoot()};
            TreePath path = new TreePath(objPath);
            this$0.addSelectionPath(path);
        }
    }
    {
    }
}
