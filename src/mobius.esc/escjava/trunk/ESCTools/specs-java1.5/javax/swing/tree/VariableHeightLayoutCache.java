package javax.swing.tree;

import javax.swing.event.TreeModelEvent;
import java.awt.Rectangle;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Stack;
import java.util.Vector;

public class VariableHeightLayoutCache extends AbstractLayoutCache {
    
    /*synthetic*/ static void access$700(VariableHeightLayoutCache x0) {
        x0.visibleNodesChanged();
    }
    
    /*synthetic*/ static VariableHeightLayoutCache$TreeStateNode access$600(VariableHeightLayoutCache x0, Object x1) {
        return x0.createNodeForValue(x1);
    }
    
    /*synthetic*/ static boolean access$502(VariableHeightLayoutCache x0, boolean x1) {
        return x0.updateNodeSizes = x1;
    }
    
    /*synthetic*/ static boolean access$500(VariableHeightLayoutCache x0) {
        return x0.updateNodeSizes;
    }
    
    /*synthetic*/ static Rectangle access$400(VariableHeightLayoutCache x0) {
        return x0.boundsBuffer;
    }
    
    /*synthetic*/ static void access$300(VariableHeightLayoutCache x0, VariableHeightLayoutCache$TreeStateNode x1) {
        x0.removeMapping(x1);
    }
    
    /*synthetic*/ static VariableHeightLayoutCache$TreeStateNode access$200(VariableHeightLayoutCache x0) {
        return x0.root;
    }
    
    /*synthetic*/ static Vector access$100(VariableHeightLayoutCache x0) {
        return x0.visibleNodes;
    }
    
    /*synthetic*/ static void access$000(VariableHeightLayoutCache x0, VariableHeightLayoutCache$TreeStateNode x1) {
        x0.addMapping(x1);
    }
    private Vector visibleNodes;
    private boolean updateNodeSizes;
    private VariableHeightLayoutCache$TreeStateNode root;
    private Rectangle boundsBuffer;
    private Hashtable treePathMapping;
    private Stack tempStacks;
    
    public VariableHeightLayoutCache() {
        
        tempStacks = new Stack();
        visibleNodes = new Vector();
        boundsBuffer = new Rectangle();
        treePathMapping = new Hashtable();
    }
    
    public void setModel(TreeModel newModel) {
        super.setModel(newModel);
        rebuild(false);
    }
    
    public void setRootVisible(boolean rootVisible) {
        if (isRootVisible() != rootVisible && root != null) {
            if (rootVisible) {
                root.updatePreferredSize(0);
                visibleNodes.insertElementAt(root, 0);
            } else if (visibleNodes.size() > 0) {
                visibleNodes.removeElementAt(0);
                if (treeSelectionModel != null) treeSelectionModel.removeSelectionPath(root.getTreePath());
            }
            if (treeSelectionModel != null) treeSelectionModel.resetRowSelection();
            if (getRowCount() > 0) getNode(0).setYOrigin(0);
            updateYLocationsFrom(0);
            visibleNodesChanged();
        }
        super.setRootVisible(rootVisible);
    }
    
    public void setRowHeight(int rowHeight) {
        if (rowHeight != getRowHeight()) {
            super.setRowHeight(rowHeight);
            invalidateSizes();
            this.visibleNodesChanged();
        }
    }
    
    public void setNodeDimensions(AbstractLayoutCache$NodeDimensions nd) {
        super.setNodeDimensions(nd);
        invalidateSizes();
        visibleNodesChanged();
    }
    
    public void setExpandedState(TreePath path, boolean isExpanded) {
        if (path != null) {
            if (isExpanded) ensurePathIsExpanded(path, true); else {
                VariableHeightLayoutCache$TreeStateNode node = getNodeForPath(path, false, true);
                if (node != null) {
                    node.makeVisible();
                    node.collapse();
                }
            }
        }
    }
    
    public boolean getExpandedState(TreePath path) {
        VariableHeightLayoutCache$TreeStateNode node = getNodeForPath(path, true, false);
        return (node != null) ? (node.isVisible() && node.isExpanded()) : false;
    }
    
    public Rectangle getBounds(TreePath path, Rectangle placeIn) {
        VariableHeightLayoutCache$TreeStateNode node = getNodeForPath(path, true, false);
        if (node != null) {
            if (updateNodeSizes) updateNodeSizes(false);
            return node.getNodeBounds(placeIn);
        }
        return null;
    }
    
    public TreePath getPathForRow(int row) {
        if (row >= 0 && row < getRowCount()) {
            return getNode(row).getTreePath();
        }
        return null;
    }
    
    public int getRowForPath(TreePath path) {
        if (path == null) return -1;
        VariableHeightLayoutCache$TreeStateNode visNode = getNodeForPath(path, true, false);
        if (visNode != null) return visNode.getRow();
        return -1;
    }
    
    public int getRowCount() {
        return visibleNodes.size();
    }
    
    public void invalidatePathBounds(TreePath path) {
        VariableHeightLayoutCache$TreeStateNode node = getNodeForPath(path, true, false);
        if (node != null) {
            node.markSizeInvalid();
            if (node.isVisible()) updateYLocationsFrom(node.getRow());
        }
    }
    
    public int getPreferredHeight() {
        int rowCount = getRowCount();
        if (rowCount > 0) {
            VariableHeightLayoutCache$TreeStateNode node = getNode(rowCount - 1);
            return node.getYOrigin() + node.getPreferredHeight();
        }
        return 0;
    }
    
    public int getPreferredWidth(Rectangle bounds) {
        if (updateNodeSizes) updateNodeSizes(false);
        return getMaxNodeWidth();
    }
    
    public TreePath getPathClosestTo(int x, int y) {
        if (getRowCount() == 0) return null;
        if (updateNodeSizes) updateNodeSizes(false);
        int row = getRowContainingYLocation(y);
        return getNode(row).getTreePath();
    }
    
    public Enumeration getVisiblePathsFrom(TreePath path) {
        VariableHeightLayoutCache$TreeStateNode node = getNodeForPath(path, true, false);
        if (node != null) {
            return new VariableHeightLayoutCache$VisibleTreeStateNodeEnumeration(this, node);
        }
        return null;
    }
    
    public int getVisibleChildCount(TreePath path) {
        VariableHeightLayoutCache$TreeStateNode node = getNodeForPath(path, true, false);
        return (node != null) ? node.getVisibleChildCount() : 0;
    }
    
    public void invalidateSizes() {
        if (root != null) root.deepMarkSizeInvalid();
        if (!isFixedRowHeight() && visibleNodes.size() > 0) {
            updateNodeSizes(true);
        }
    }
    
    public boolean isExpanded(TreePath path) {
        if (path != null) {
            VariableHeightLayoutCache$TreeStateNode lastNode = getNodeForPath(path, true, false);
            return (lastNode != null && lastNode.isExpanded());
        }
        return false;
    }
    
    public void treeNodesChanged(TreeModelEvent e) {
        if (e != null) {
            int[] changedIndexs;
            VariableHeightLayoutCache$TreeStateNode changedNode;
            changedIndexs = e.getChildIndices();
            changedNode = getNodeForPath(e.getTreePath(), false, false);
            if (changedNode != null) {
                Object changedValue = changedNode.getValue();
                changedNode.updatePreferredSize();
                if (changedNode.hasBeenExpanded() && changedIndexs != null) {
                    int counter;
                    VariableHeightLayoutCache$TreeStateNode changedChildNode;
                    for (counter = 0; counter < changedIndexs.length; counter++) {
                        changedChildNode = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)changedNode.getChildAt(changedIndexs[counter]);
                        changedChildNode.setUserObject(treeModel.getChild(changedValue, changedIndexs[counter]));
                        changedChildNode.updatePreferredSize();
                    }
                } else if (changedNode == root) {
                    changedNode.updatePreferredSize();
                }
                if (!isFixedRowHeight()) {
                    int aRow = changedNode.getRow();
                    if (aRow != -1) this.updateYLocationsFrom(aRow);
                }
                this.visibleNodesChanged();
            }
        }
    }
    
    public void treeNodesInserted(TreeModelEvent e) {
        if (e != null) {
            int[] changedIndexs;
            VariableHeightLayoutCache$TreeStateNode changedParentNode;
            changedIndexs = e.getChildIndices();
            changedParentNode = getNodeForPath(e.getTreePath(), false, false);
            if (changedParentNode != null && changedIndexs != null && changedIndexs.length > 0) {
                if (changedParentNode.hasBeenExpanded()) {
                    boolean makeVisible;
                    int counter;
                    Object changedParent;
                    VariableHeightLayoutCache$TreeStateNode newNode;
                    int oldChildCount = changedParentNode.getChildCount();
                    changedParent = changedParentNode.getValue();
                    makeVisible = ((changedParentNode == root && !rootVisible) || (changedParentNode.getRow() != -1 && changedParentNode.isExpanded()));
                    for (counter = 0; counter < changedIndexs.length; counter++) {
                        newNode = this.createNodeAt(changedParentNode, changedIndexs[counter]);
                    }
                    if (oldChildCount == 0) {
                        changedParentNode.updatePreferredSize();
                    }
                    if (treeSelectionModel != null) treeSelectionModel.resetRowSelection();
                    if (!isFixedRowHeight() && (makeVisible || (oldChildCount == 0 && changedParentNode.isVisible()))) {
                        if (changedParentNode == root) this.updateYLocationsFrom(0); else this.updateYLocationsFrom(changedParentNode.getRow());
                        this.visibleNodesChanged();
                    } else if (makeVisible) this.visibleNodesChanged();
                } else if (treeModel.getChildCount(changedParentNode.getValue()) - changedIndexs.length == 0) {
                    changedParentNode.updatePreferredSize();
                    if (!isFixedRowHeight() && changedParentNode.isVisible()) updateYLocationsFrom(changedParentNode.getRow());
                }
            }
        }
    }
    
    public void treeNodesRemoved(TreeModelEvent e) {
        if (e != null) {
            int[] changedIndexs;
            VariableHeightLayoutCache$TreeStateNode changedParentNode;
            changedIndexs = e.getChildIndices();
            changedParentNode = getNodeForPath(e.getTreePath(), false, false);
            if (changedParentNode != null && changedIndexs != null && changedIndexs.length > 0) {
                if (changedParentNode.hasBeenExpanded()) {
                    boolean makeInvisible;
                    int counter;
                    int removedRow;
                    VariableHeightLayoutCache$TreeStateNode removedNode;
                    makeInvisible = ((changedParentNode == root && !rootVisible) || (changedParentNode.getRow() != -1 && changedParentNode.isExpanded()));
                    for (counter = changedIndexs.length - 1; counter >= 0; counter--) {
                        removedNode = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)changedParentNode.getChildAt(changedIndexs[counter]);
                        if (removedNode.isExpanded()) {
                            removedNode.collapse(false);
                        }
                        if (makeInvisible) {
                            removedRow = removedNode.getRow();
                            if (removedRow != -1) {
                                visibleNodes.removeElementAt(removedRow);
                            }
                        }
                        changedParentNode.remove(changedIndexs[counter]);
                    }
                    if (changedParentNode.getChildCount() == 0) {
                        changedParentNode.updatePreferredSize();
                        if (changedParentNode.isExpanded() && changedParentNode.isLeaf()) {
                            changedParentNode.collapse(false);
                        }
                    }
                    if (treeSelectionModel != null) treeSelectionModel.resetRowSelection();
                    if (!isFixedRowHeight() && (makeInvisible || (changedParentNode.getChildCount() == 0 && changedParentNode.isVisible()))) {
                        if (changedParentNode == root) {
                            if (getRowCount() > 0) getNode(0).setYOrigin(0);
                            updateYLocationsFrom(0);
                        } else updateYLocationsFrom(changedParentNode.getRow());
                        this.visibleNodesChanged();
                    } else if (makeInvisible) this.visibleNodesChanged();
                } else if (treeModel.getChildCount(changedParentNode.getValue()) == 0) {
                    changedParentNode.updatePreferredSize();
                    if (!isFixedRowHeight() && changedParentNode.isVisible()) this.updateYLocationsFrom(changedParentNode.getRow());
                }
            }
        }
    }
    
    public void treeStructureChanged(TreeModelEvent e) {
        if (e != null) {
            TreePath changedPath = e.getTreePath();
            VariableHeightLayoutCache$TreeStateNode changedNode;
            changedNode = getNodeForPath(changedPath, false, false);
            if (changedNode == root || (changedNode == null && ((changedPath == null && treeModel != null && treeModel.getRoot() == null) || (changedPath != null && changedPath.getPathCount() == 1)))) {
                rebuild(true);
            } else if (changedNode != null) {
                int nodeIndex;
                int oldRow;
                VariableHeightLayoutCache$TreeStateNode newNode;
                VariableHeightLayoutCache$TreeStateNode parent;
                boolean wasExpanded;
                boolean wasVisible;
                int newIndex;
                wasExpanded = changedNode.isExpanded();
                wasVisible = (changedNode.getRow() != -1);
                parent = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)changedNode.getParent();
                nodeIndex = parent.getIndex(changedNode);
                if (wasVisible && wasExpanded) {
                    changedNode.collapse(false);
                }
                if (wasVisible) visibleNodes.removeElement(changedNode);
                changedNode.removeFromParent();
                createNodeAt(parent, nodeIndex);
                newNode = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)parent.getChildAt(nodeIndex);
                if (wasVisible && wasExpanded) newNode.expand(false);
                newIndex = newNode.getRow();
                if (!isFixedRowHeight() && wasVisible) {
                    if (newIndex == 0) updateYLocationsFrom(newIndex); else updateYLocationsFrom(newIndex - 1);
                    this.visibleNodesChanged();
                } else if (wasVisible) this.visibleNodesChanged();
            }
        }
    }
    
    private void visibleNodesChanged() {
    }
    
    private void addMapping(VariableHeightLayoutCache$TreeStateNode node) {
        treePathMapping.put(node.getTreePath(), node);
    }
    
    private void removeMapping(VariableHeightLayoutCache$TreeStateNode node) {
        treePathMapping.remove(node.getTreePath());
    }
    
    private VariableHeightLayoutCache$TreeStateNode getMapping(TreePath path) {
        return (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)treePathMapping.get(path);
    }
    
    private Rectangle getBounds(int row, Rectangle placeIn) {
        if (updateNodeSizes) updateNodeSizes(false);
        if (row >= 0 && row < getRowCount()) {
            return getNode(row).getNodeBounds(placeIn);
        }
        return null;
    }
    
    private void rebuild(boolean clearSelection) {
        Object rootObject;
        treePathMapping.clear();
        if (treeModel != null && (rootObject = treeModel.getRoot()) != null) {
            root = createNodeForValue(rootObject);
            root.path = new TreePath(rootObject);
            addMapping(root);
            root.updatePreferredSize(0);
            visibleNodes.removeAllElements();
            if (isRootVisible()) visibleNodes.addElement(root);
            if (!root.isExpanded()) root.expand(); else {
                Enumeration cursor = root.children();
                while (cursor.hasMoreElements()) {
                    visibleNodes.addElement(cursor.nextElement());
                }
                if (!isFixedRowHeight()) updateYLocationsFrom(0);
            }
        } else {
            visibleNodes.removeAllElements();
            root = null;
        }
        if (clearSelection && treeSelectionModel != null) {
            treeSelectionModel.clearSelection();
        }
        this.visibleNodesChanged();
    }
    
    private VariableHeightLayoutCache$TreeStateNode createNodeAt(VariableHeightLayoutCache$TreeStateNode parent, int childIndex) {
        boolean isParentRoot;
        Object newValue;
        VariableHeightLayoutCache$TreeStateNode newChildNode;
        newValue = treeModel.getChild(parent.getValue(), childIndex);
        newChildNode = createNodeForValue(newValue);
        parent.insert(newChildNode, childIndex);
        newChildNode.updatePreferredSize(-1);
        isParentRoot = (parent == root);
        if (newChildNode != null && parent.isExpanded() && (parent.getRow() != -1 || isParentRoot)) {
            int newRow;
            if (childIndex == 0) {
                if (isParentRoot && !isRootVisible()) newRow = 0; else newRow = parent.getRow() + 1;
            } else if (childIndex == parent.getChildCount()) newRow = parent.getLastVisibleNode().getRow() + 1; else {
                VariableHeightLayoutCache$TreeStateNode previousNode;
                previousNode = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)parent.getChildAt(childIndex - 1);
                newRow = previousNode.getLastVisibleNode().getRow() + 1;
            }
            visibleNodes.insertElementAt(newChildNode, newRow);
        }
        return newChildNode;
    }
    
    private VariableHeightLayoutCache$TreeStateNode getNodeForPath(TreePath path, boolean onlyIfVisible, boolean shouldCreate) {
        if (path != null) {
            VariableHeightLayoutCache$TreeStateNode node;
            node = getMapping(path);
            if (node != null) {
                if (onlyIfVisible && !node.isVisible()) return null;
                return node;
            }
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
                            node.getLoadedChildren(shouldCreate);
                            int childIndex = treeModel.getIndexOfChild(node.getUserObject(), path.getLastPathComponent());
                            if (childIndex == -1 || childIndex >= node.getChildCount() || (onlyIfVisible && !node.isVisible())) {
                                node = null;
                            } else node = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)node.getChildAt(childIndex);
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
        }
        return null;
    }
    
    private void updateYLocationsFrom(int location) {
        if (location >= 0 && location < getRowCount()) {
            int counter;
            int maxCounter;
            int newYOrigin;
            VariableHeightLayoutCache$TreeStateNode aNode;
            aNode = getNode(location);
            newYOrigin = aNode.getYOrigin() + aNode.getPreferredHeight();
            for (counter = location + 1, maxCounter = visibleNodes.size(); counter < maxCounter; counter++) {
                aNode = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)visibleNodes.elementAt(counter);
                aNode.setYOrigin(newYOrigin);
                newYOrigin += aNode.getPreferredHeight();
            }
        }
    }
    
    private void updateNodeSizes(boolean updateAll) {
        int aY;
        int counter;
        int maxCounter;
        VariableHeightLayoutCache$TreeStateNode node;
        updateNodeSizes = false;
        for (aY = counter = 0, maxCounter = visibleNodes.size(); counter < maxCounter; counter++) {
            node = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)visibleNodes.elementAt(counter);
            node.setYOrigin(aY);
            if (updateAll || !node.hasValidSize()) node.updatePreferredSize(counter);
            aY += node.getPreferredHeight();
        }
    }
    
    private int getRowContainingYLocation(int location) {
        if (isFixedRowHeight()) {
            if (getRowCount() == 0) return -1;
            return Math.max(0, Math.min(getRowCount() - 1, location / getRowHeight()));
        }
        int max;
        int maxY;
        int mid;
        int min;
        int minY;
        VariableHeightLayoutCache$TreeStateNode node;
        if ((max = getRowCount()) <= 0) return -1;
        mid = min = 0;
        while (min < max) {
            mid = (max - min) / 2 + min;
            node = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)visibleNodes.elementAt(mid);
            minY = node.getYOrigin();
            maxY = minY + node.getPreferredHeight();
            if (location < minY) {
                max = mid - 1;
            } else if (location >= maxY) {
                min = mid + 1;
            } else break;
        }
        if (min == max) {
            mid = min;
            if (mid >= getRowCount()) mid = getRowCount() - 1;
        }
        return mid;
    }
    
    private void ensurePathIsExpanded(TreePath aPath, boolean expandLast) {
        if (aPath != null) {
            if (treeModel.isLeaf(aPath.getLastPathComponent())) {
                aPath = aPath.getParentPath();
                expandLast = true;
            }
            if (aPath != null) {
                VariableHeightLayoutCache$TreeStateNode lastNode = getNodeForPath(aPath, false, true);
                if (lastNode != null) {
                    lastNode.makeVisible();
                    if (expandLast) lastNode.expand();
                }
            }
        }
    }
    
    private VariableHeightLayoutCache$TreeStateNode getNode(int row) {
        return (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)visibleNodes.elementAt(row);
    }
    
    private int getMaxNodeWidth() {
        int maxWidth = 0;
        int nodeWidth;
        int counter;
        VariableHeightLayoutCache$TreeStateNode node;
        for (counter = getRowCount() - 1; counter >= 0; counter--) {
            node = this.getNode(counter);
            nodeWidth = node.getPreferredWidth() + node.getXOrigin();
            if (nodeWidth > maxWidth) maxWidth = nodeWidth;
        }
        return maxWidth;
    }
    
    private VariableHeightLayoutCache$TreeStateNode createNodeForValue(Object value) {
        return new VariableHeightLayoutCache$TreeStateNode(this, value);
    }
    {
    }
    {
    }
}
