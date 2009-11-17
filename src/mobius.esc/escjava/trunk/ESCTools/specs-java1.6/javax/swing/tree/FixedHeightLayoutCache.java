package javax.swing.tree;

import javax.swing.event.TreeModelEvent;
import java.awt.Rectangle;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Stack;

public class FixedHeightLayoutCache extends AbstractLayoutCache {
    
    /*synthetic*/ static FixedHeightLayoutCache$FHTreeStateNode access$600(FixedHeightLayoutCache x0) {
        return x0.root;
    }
    
    /*synthetic*/ static int access$502(FixedHeightLayoutCache x0, int x1) {
        return x0.rowCount = x1;
    }
    
    /*synthetic*/ static void access$400(FixedHeightLayoutCache x0, int x1) {
        x0.adjustRowCountBy(x1);
    }
    
    /*synthetic*/ static FixedHeightLayoutCache$FHTreeStateNode access$300(FixedHeightLayoutCache x0, Object x1, int x2) {
        return x0.createNodeForValue(x1, x2);
    }
    
    /*synthetic*/ static void access$200(FixedHeightLayoutCache x0, FixedHeightLayoutCache$FHTreeStateNode x1) {
        x0.removeMapping(x1);
    }
    
    /*synthetic*/ static void access$100(FixedHeightLayoutCache x0, FixedHeightLayoutCache$FHTreeStateNode x1) {
        x0.addMapping(x1);
    }
    {
    }
    private FixedHeightLayoutCache$FHTreeStateNode root;
    private int rowCount;
    private Rectangle boundsBuffer;
    private Hashtable treePathMapping;
    private FixedHeightLayoutCache$SearchInfo info;
    private Stack tempStacks;
    
    public FixedHeightLayoutCache() {
        
        tempStacks = new Stack();
        boundsBuffer = new Rectangle();
        treePathMapping = new Hashtable();
        info = new FixedHeightLayoutCache$SearchInfo(this, null);
        setRowHeight(1);
    }
    
    public void setModel(TreeModel newModel) {
        super.setModel(newModel);
        rebuild(false);
    }
    
    public void setRootVisible(boolean rootVisible) {
        if (isRootVisible() != rootVisible) {
            super.setRootVisible(rootVisible);
            if (root != null) {
                if (rootVisible) {
                    rowCount++;
                    root.adjustRowBy(1);
                } else {
                    rowCount--;
                    root.adjustRowBy(-1);
                }
                visibleNodesChanged();
            }
        }
    }
    
    public void setRowHeight(int rowHeight) {
        if (rowHeight <= 0) throw new IllegalArgumentException("FixedHeightLayoutCache only supports row heights greater than 0");
        if (getRowHeight() != rowHeight) {
            super.setRowHeight(rowHeight);
            visibleNodesChanged();
        }
    }
    
    public int getRowCount() {
        return rowCount;
    }
    
    public void invalidatePathBounds(TreePath path) {
    }
    
    public void invalidateSizes() {
        visibleNodesChanged();
    }
    
    public boolean isExpanded(TreePath path) {
        if (path != null) {
            FixedHeightLayoutCache$FHTreeStateNode lastNode = getNodeForPath(path, true, false);
            return (lastNode != null && lastNode.isExpanded());
        }
        return false;
    }
    
    public Rectangle getBounds(TreePath path, Rectangle placeIn) {
        if (path == null) return null;
        FixedHeightLayoutCache$FHTreeStateNode node = getNodeForPath(path, true, false);
        if (node != null) return getBounds(node, -1, placeIn);
        TreePath parentPath = path.getParentPath();
        node = getNodeForPath(parentPath, true, false);
        if (node != null) {
            int childIndex = treeModel.getIndexOfChild(parentPath.getLastPathComponent(), path.getLastPathComponent());
            if (childIndex != -1) return getBounds(node, childIndex, placeIn);
        }
        return null;
    }
    
    public TreePath getPathForRow(int row) {
        if (row >= 0 && row < getRowCount()) {
            if (root.getPathForRow(row, getRowCount(), info)) {
                return info.getPath();
            }
        }
        return null;
    }
    
    public int getRowForPath(TreePath path) {
        if (path == null || root == null) return -1;
        FixedHeightLayoutCache$FHTreeStateNode node = getNodeForPath(path, true, false);
        if (node != null) return node.getRow();
        TreePath parentPath = path.getParentPath();
        node = getNodeForPath(parentPath, true, false);
        if (node != null && node.isExpanded()) {
            return node.getRowToModelIndex(treeModel.getIndexOfChild(parentPath.getLastPathComponent(), path.getLastPathComponent()));
        }
        return -1;
    }
    
    public TreePath getPathClosestTo(int x, int y) {
        if (getRowCount() == 0) return null;
        int row = getRowContainingYLocation(y);
        return getPathForRow(row);
    }
    
    public int getVisibleChildCount(TreePath path) {
        FixedHeightLayoutCache$FHTreeStateNode node = getNodeForPath(path, true, false);
        if (node == null) return 0;
        return node.getTotalChildCount();
    }
    
    public Enumeration getVisiblePathsFrom(TreePath path) {
        if (path == null) return null;
        FixedHeightLayoutCache$FHTreeStateNode node = getNodeForPath(path, true, false);
        if (node != null) {
            return new FixedHeightLayoutCache$VisibleFHTreeStateNodeEnumeration(this, node);
        }
        TreePath parentPath = path.getParentPath();
        node = getNodeForPath(parentPath, true, false);
        if (node != null && node.isExpanded()) {
            return new FixedHeightLayoutCache$VisibleFHTreeStateNodeEnumeration(this, node, treeModel.getIndexOfChild(parentPath.getLastPathComponent(), path.getLastPathComponent()));
        }
        return null;
    }
    
    public void setExpandedState(TreePath path, boolean isExpanded) {
        if (isExpanded) ensurePathIsExpanded(path, true); else if (path != null) {
            TreePath parentPath = path.getParentPath();
            if (parentPath != null) {
                FixedHeightLayoutCache$FHTreeStateNode parentNode = getNodeForPath(parentPath, false, true);
                if (parentNode != null) parentNode.makeVisible();
            }
            FixedHeightLayoutCache$FHTreeStateNode childNode = getNodeForPath(path, true, false);
            if (childNode != null) childNode.collapse(true);
        }
    }
    
    public boolean getExpandedState(TreePath path) {
        FixedHeightLayoutCache$FHTreeStateNode node = getNodeForPath(path, true, false);
        return (node != null) ? (node.isVisible() && node.isExpanded()) : false;
    }
    
    public void treeNodesChanged(TreeModelEvent e) {
        if (e != null) {
            int[] changedIndexs;
            FixedHeightLayoutCache$FHTreeStateNode changedParent = getNodeForPath(e.getTreePath(), false, false);
            int maxCounter;
            changedIndexs = e.getChildIndices();
            if (changedParent != null) {
                if (changedIndexs != null && (maxCounter = changedIndexs.length) > 0) {
                    Object parentValue = changedParent.getUserObject();
                    for (int counter = 0; counter < maxCounter; counter++) {
                        FixedHeightLayoutCache$FHTreeStateNode child = changedParent.getChildAtModelIndex(changedIndexs[counter]);
                        if (child != null) {
                            child.setUserObject(treeModel.getChild(parentValue, changedIndexs[counter]));
                        }
                    }
                    if (changedParent.isVisible() && changedParent.isExpanded()) visibleNodesChanged();
                } else if (changedParent == root && changedParent.isVisible() && changedParent.isExpanded()) {
                    visibleNodesChanged();
                }
            }
        }
    }
    
    public void treeNodesInserted(TreeModelEvent e) {
        if (e != null) {
            int[] changedIndexs;
            FixedHeightLayoutCache$FHTreeStateNode changedParent = getNodeForPath(e.getTreePath(), false, false);
            int maxCounter;
            changedIndexs = e.getChildIndices();
            if (changedParent != null && changedIndexs != null && (maxCounter = changedIndexs.length) > 0) {
                boolean isVisible = (changedParent.isVisible() && changedParent.isExpanded());
                for (int counter = 0; counter < maxCounter; counter++) {
                    changedParent.childInsertedAtModelIndex(changedIndexs[counter], isVisible);
                }
                if (isVisible && treeSelectionModel != null) treeSelectionModel.resetRowSelection();
                if (changedParent.isVisible()) this.visibleNodesChanged();
            }
        }
    }
    
    public void treeNodesRemoved(TreeModelEvent e) {
        if (e != null) {
            int[] changedIndexs;
            int maxCounter;
            TreePath parentPath = e.getTreePath();
            FixedHeightLayoutCache$FHTreeStateNode changedParentNode = getNodeForPath(parentPath, false, false);
            changedIndexs = e.getChildIndices();
            if (changedParentNode != null && changedIndexs != null && (maxCounter = changedIndexs.length) > 0) {
                Object[] children = e.getChildren();
                boolean isVisible = (changedParentNode.isVisible() && changedParentNode.isExpanded());
                for (int counter = maxCounter - 1; counter >= 0; counter--) {
                    changedParentNode.removeChildAtModelIndex(changedIndexs[counter], isVisible);
                }
                if (isVisible) {
                    if (treeSelectionModel != null) treeSelectionModel.resetRowSelection();
                    if (treeModel.getChildCount(changedParentNode.getUserObject()) == 0 && changedParentNode.isLeaf()) {
                        changedParentNode.collapse(false);
                    }
                    visibleNodesChanged();
                } else if (changedParentNode.isVisible()) visibleNodesChanged();
            }
        }
    }
    
    public void treeStructureChanged(TreeModelEvent e) {
        if (e != null) {
            TreePath changedPath = e.getTreePath();
            FixedHeightLayoutCache$FHTreeStateNode changedNode = getNodeForPath(changedPath, false, false);
            if (changedNode == root || (changedNode == null && ((changedPath == null && treeModel != null && treeModel.getRoot() == null) || (changedPath != null && changedPath.getPathCount() <= 1)))) {
                rebuild(true);
            } else if (changedNode != null) {
                boolean wasExpanded;
                boolean wasVisible;
                FixedHeightLayoutCache$FHTreeStateNode parent = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)changedNode.getParent();
                wasExpanded = changedNode.isExpanded();
                wasVisible = changedNode.isVisible();
                int index = parent.getIndex(changedNode);
                changedNode.collapse(false);
                parent.remove(index);
                if (wasVisible && wasExpanded) {
                    int row = changedNode.getRow();
                    parent.resetChildrenRowsFrom(row, index, changedNode.getChildIndex());
                    changedNode = getNodeForPath(changedPath, false, true);
                    changedNode.expand();
                }
                if (treeSelectionModel != null && wasVisible && wasExpanded) treeSelectionModel.resetRowSelection();
                if (wasVisible) this.visibleNodesChanged();
            }
        }
    }
    
    private void visibleNodesChanged() {
    }
    
    private Rectangle getBounds(FixedHeightLayoutCache$FHTreeStateNode parent, int childIndex, Rectangle placeIn) {
        boolean expanded;
        int level;
        int row;
        Object value;
        if (childIndex == -1) {
            row = parent.getRow();
            value = parent.getUserObject();
            expanded = parent.isExpanded();
            level = parent.getLevel();
        } else {
            row = parent.getRowToModelIndex(childIndex);
            value = treeModel.getChild(parent.getUserObject(), childIndex);
            expanded = false;
            level = parent.getLevel() + 1;
        }
        Rectangle bounds = getNodeDimensions(value, row, level, expanded, boundsBuffer);
        if (bounds == null) return null;
        if (placeIn == null) placeIn = new Rectangle();
        placeIn.x = bounds.x;
        placeIn.height = getRowHeight();
        placeIn.y = row * placeIn.height;
        placeIn.width = bounds.width;
        return placeIn;
    }
    
    private void adjustRowCountBy(int changeAmount) {
        rowCount += changeAmount;
    }
    
    private void addMapping(FixedHeightLayoutCache$FHTreeStateNode node) {
        treePathMapping.put(node.getTreePath(), node);
    }
    
    private void removeMapping(FixedHeightLayoutCache$FHTreeStateNode node) {
        treePathMapping.remove(node.getTreePath());
    }
    
    private FixedHeightLayoutCache$FHTreeStateNode getMapping(TreePath path) {
        return (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)treePathMapping.get(path);
    }
    
    private void rebuild(boolean clearSelection) {
        Object rootUO;
        treePathMapping.clear();
        if (treeModel != null && (rootUO = treeModel.getRoot()) != null) {
            root = createNodeForValue(rootUO, 0);
            root.path = new TreePath(rootUO);
            addMapping(root);
            if (isRootVisible()) {
                rowCount = 1;
                root.row = 0;
            } else {
                rowCount = 0;
                root.row = -1;
            }
            root.expand();
        } else {
            root = null;
            rowCount = 0;
        }
        if (clearSelection && treeSelectionModel != null) {
            treeSelectionModel.clearSelection();
        }
        this.visibleNodesChanged();
    }
    
    private int getRowContainingYLocation(int location) {
        if (getRowCount() == 0) return -1;
        return Math.max(0, Math.min(getRowCount() - 1, location / getRowHeight()));
    }
    
    private boolean ensurePathIsExpanded(TreePath aPath, boolean expandLast) {
        if (aPath != null) {
            if (treeModel.isLeaf(aPath.getLastPathComponent())) {
                aPath = aPath.getParentPath();
                expandLast = true;
            }
            if (aPath != null) {
                FixedHeightLayoutCache$FHTreeStateNode lastNode = getNodeForPath(aPath, false, true);
                if (lastNode != null) {
                    lastNode.makeVisible();
                    if (expandLast) lastNode.expand();
                    return true;
                }
            }
        }
        return false;
    }
    
    private FixedHeightLayoutCache$FHTreeStateNode createNodeForValue(Object value, int childIndex) {
        return new FixedHeightLayoutCache$FHTreeStateNode(this, value, childIndex, -1);
    }
    
    private FixedHeightLayoutCache$FHTreeStateNode getNodeForPath(TreePath path, boolean onlyIfVisible, boolean shouldCreate) {
        if (path != null) {
            FixedHeightLayoutCache$FHTreeStateNode node;
            node = getMapping(path);
            if (node != null) {
                if (onlyIfVisible && !node.isVisible()) return null;
                return node;
            }
            if (onlyIfVisible) return null;
            Stack paths;
            if (tempStacks.size() == 0) {
                paths = new Stack();
            } else {
                paths = (Stack)(Stack)tempStacks.pop();
            }
            try {
                paths.push(path);
                path = path.getParentPath();
                node = null;
                while (path != null) {
                    node = getMapping(path);
                    if (node != null) {
                        while (node != null && paths.size() > 0) {
                            path = (TreePath)(TreePath)paths.pop();
                            node = node.createChildFor(path.getLastPathComponent());
                        }
                        return node;
                    }
                    paths.push(path);
                    path = path.getParentPath();
                }
            } finally {
                paths.removeAllElements();
                tempStacks.push(paths);
            }
            return null;
        }
        return null;
    }
    {
    }
    {
    }
    {
    }
}
