package javax.swing.tree;

class FixedHeightLayoutCache$FHTreeStateNode extends DefaultMutableTreeNode {
    /*synthetic*/ final FixedHeightLayoutCache this$0;
    protected boolean isExpanded;
    protected int childIndex;
    protected int childCount;
    protected int row;
    protected TreePath path;
    
    public FixedHeightLayoutCache$FHTreeStateNode(/*synthetic*/ final FixedHeightLayoutCache this$0, Object userObject, int childIndex, int row) {
        this.this$0 = this$0;
        super(userObject);
        this.childIndex = childIndex;
        this.row = row;
    }
    
    public void setParent(MutableTreeNode parent) {
        super.setParent(parent);
        if (parent != null) {
            path = ((FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)parent).getTreePath().pathByAddingChild(getUserObject());
            FixedHeightLayoutCache.access$100(this$0, this);
        }
    }
    
    public void remove(int childIndex) {
        FixedHeightLayoutCache$FHTreeStateNode node = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(childIndex);
        node.removeFromMapping();
        super.remove(childIndex);
    }
    
    public void setUserObject(Object o) {
        super.setUserObject(o);
        if (path != null) {
            FixedHeightLayoutCache$FHTreeStateNode parent = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getParent();
            if (parent != null) resetChildrenPaths(parent.getTreePath()); else resetChildrenPaths(null);
        }
    }
    
    public int getChildIndex() {
        return childIndex;
    }
    
    public TreePath getTreePath() {
        return path;
    }
    
    public FixedHeightLayoutCache$FHTreeStateNode getChildAtModelIndex(int index) {
        for (int counter = getChildCount() - 1; counter >= 0; counter--) if (((FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter)).childIndex == index) return (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter);
        return null;
    }
    
    public boolean isVisible() {
        FixedHeightLayoutCache$FHTreeStateNode parent = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getParent();
        if (parent == null) return true;
        return (parent.isExpanded() && parent.isVisible());
    }
    
    public int getRow() {
        return row;
    }
    
    public int getRowToModelIndex(int index) {
        FixedHeightLayoutCache$FHTreeStateNode child;
        int lastRow = getRow() + 1;
        int retValue = lastRow;
        for (int counter = 0, maxCounter = getChildCount(); counter < maxCounter; counter++) {
            child = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter);
            if (child.childIndex >= index) {
                if (child.childIndex == index) return child.row;
                if (counter == 0) return getRow() + 1 + index;
                return child.row - (child.childIndex - index);
            }
        }
        return getRow() + 1 + getTotalChildCount() - (childCount - index);
    }
    
    public int getTotalChildCount() {
        if (isExpanded()) {
            FixedHeightLayoutCache$FHTreeStateNode parent = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getParent();
            int pIndex;
            if (parent != null && (pIndex = parent.getIndex(this)) + 1 < parent.getChildCount()) {
                FixedHeightLayoutCache$FHTreeStateNode nextSibling = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)parent.getChildAt(pIndex + 1);
                return nextSibling.row - row - (nextSibling.childIndex - childIndex);
            } else {
                int retCount = childCount;
                for (int counter = getChildCount() - 1; counter >= 0; counter--) {
                    retCount += ((FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter)).getTotalChildCount();
                }
                return retCount;
            }
        }
        return 0;
    }
    
    public boolean isExpanded() {
        return isExpanded;
    }
    
    public int getVisibleLevel() {
        if (this$0.isRootVisible()) {
            return getLevel();
        } else {
            return getLevel() - 1;
        }
    }
    
    protected void resetChildrenPaths(TreePath parentPath) {
        FixedHeightLayoutCache.access$200(this$0, this);
        if (parentPath == null) path = new TreePath(getUserObject()); else path = parentPath.pathByAddingChild(getUserObject());
        FixedHeightLayoutCache.access$100(this$0, this);
        for (int counter = getChildCount() - 1; counter >= 0; counter--) ((FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter)).resetChildrenPaths(path);
    }
    
    protected void removeFromMapping() {
        if (path != null) {
            FixedHeightLayoutCache.access$200(this$0, this);
            for (int counter = getChildCount() - 1; counter >= 0; counter--) ((FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter)).removeFromMapping();
        }
    }
    
    protected FixedHeightLayoutCache$FHTreeStateNode createChildFor(Object userObject) {
        int newChildIndex = this$0.treeModel.getIndexOfChild(getUserObject(), userObject);
        if (newChildIndex < 0) return null;
        FixedHeightLayoutCache$FHTreeStateNode aNode;
        FixedHeightLayoutCache$FHTreeStateNode child = FixedHeightLayoutCache.access$300(this$0, userObject, newChildIndex);
        int childRow;
        if (isVisible()) {
            childRow = getRowToModelIndex(newChildIndex);
        } else {
            childRow = -1;
        }
        child.row = childRow;
        for (int counter = 0, maxCounter = getChildCount(); counter < maxCounter; counter++) {
            aNode = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter);
            if (aNode.childIndex > newChildIndex) {
                insert(child, counter);
                return child;
            }
        }
        add(child);
        return child;
    }
    
    protected void adjustRowBy(int amount) {
        row += amount;
        if (isExpanded) {
            for (int counter = getChildCount() - 1; counter >= 0; counter--) ((FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter)).adjustRowBy(amount);
        }
    }
    
    protected void adjustRowBy(int amount, int startIndex) {
        if (isExpanded) {
            for (int counter = getChildCount() - 1; counter >= startIndex; counter--) ((FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter)).adjustRowBy(amount);
        }
        FixedHeightLayoutCache$FHTreeStateNode parent = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getParent();
        if (parent != null) {
            parent.adjustRowBy(amount, parent.getIndex(this) + 1);
        }
    }
    
    protected void didExpand() {
        int nextRow = setRowAndChildren(row);
        FixedHeightLayoutCache$FHTreeStateNode parent = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getParent();
        int childRowCount = nextRow - row - 1;
        if (parent != null) {
            parent.adjustRowBy(childRowCount, parent.getIndex(this) + 1);
        }
        FixedHeightLayoutCache.access$400(this$0, childRowCount);
    }
    
    protected int setRowAndChildren(int nextRow) {
        row = nextRow;
        if (!isExpanded()) return row + 1;
        int lastRow = row + 1;
        int lastModelIndex = 0;
        FixedHeightLayoutCache$FHTreeStateNode child;
        int maxCounter = getChildCount();
        for (int counter = 0; counter < maxCounter; counter++) {
            child = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter);
            lastRow += (child.childIndex - lastModelIndex);
            lastModelIndex = child.childIndex + 1;
            if (child.isExpanded) {
                lastRow = child.setRowAndChildren(lastRow);
            } else {
                child.row = lastRow++;
            }
        }
        return lastRow + childCount - lastModelIndex;
    }
    
    protected void resetChildrenRowsFrom(int newRow, int childIndex, int modelIndex) {
        int lastRow = newRow;
        int lastModelIndex = modelIndex;
        FixedHeightLayoutCache$FHTreeStateNode node;
        int maxCounter = getChildCount();
        for (int counter = childIndex; counter < maxCounter; counter++) {
            node = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter);
            lastRow += (node.childIndex - lastModelIndex);
            lastModelIndex = node.childIndex + 1;
            if (node.isExpanded) {
                lastRow = node.setRowAndChildren(lastRow);
            } else {
                node.row = lastRow++;
            }
        }
        lastRow += childCount - lastModelIndex;
        node = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getParent();
        if (node != null) {
            node.resetChildrenRowsFrom(lastRow, node.getIndex(this) + 1, this.childIndex + 1);
        } else {
            FixedHeightLayoutCache.access$502(this$0, lastRow);
        }
    }
    
    protected void makeVisible() {
        FixedHeightLayoutCache$FHTreeStateNode parent = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getParent();
        if (parent != null) parent.expandParentAndReceiver();
    }
    
    protected void expandParentAndReceiver() {
        FixedHeightLayoutCache$FHTreeStateNode parent = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getParent();
        if (parent != null) parent.expandParentAndReceiver();
        expand();
    }
    
    protected void expand() {
        if (!isExpanded && !isLeaf()) {
            boolean visible = isVisible();
            isExpanded = true;
            childCount = this$0.treeModel.getChildCount(getUserObject());
            if (visible) {
                didExpand();
            }
            if (visible && this$0.treeSelectionModel != null) {
                this$0.treeSelectionModel.resetRowSelection();
            }
        }
    }
    
    protected void collapse(boolean adjustRows) {
        if (isExpanded) {
            if (isVisible() && adjustRows) {
                int childCount = getTotalChildCount();
                isExpanded = false;
                FixedHeightLayoutCache.access$400(this$0, -childCount);
                adjustRowBy(-childCount, 0);
            } else isExpanded = false;
            if (adjustRows && isVisible() && this$0.treeSelectionModel != null) this$0.treeSelectionModel.resetRowSelection();
        }
    }
    
    public boolean isLeaf() {
        TreeModel model = this$0.getModel();
        return (model != null) ? model.isLeaf(this.getUserObject()) : true;
    }
    
    protected void addNode(FixedHeightLayoutCache$FHTreeStateNode newChild) {
        boolean added = false;
        int childIndex = newChild.getChildIndex();
        for (int counter = 0, maxCounter = getChildCount(); counter < maxCounter; counter++) {
            if (((FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter)).getChildIndex() > childIndex) {
                added = true;
                insert(newChild, counter);
                counter = maxCounter;
            }
        }
        if (!added) add(newChild);
    }
    
    protected void removeChildAtModelIndex(int modelIndex, boolean isChildVisible) {
        FixedHeightLayoutCache$FHTreeStateNode childNode = getChildAtModelIndex(modelIndex);
        if (childNode != null) {
            int row = childNode.getRow();
            int index = getIndex(childNode);
            childNode.collapse(false);
            remove(index);
            adjustChildIndexs(index, -1);
            childCount--;
            if (isChildVisible) {
                resetChildrenRowsFrom(row, index, modelIndex);
            }
        } else {
            int maxCounter = getChildCount();
            FixedHeightLayoutCache$FHTreeStateNode aChild;
            for (int counter = 0; counter < maxCounter; counter++) {
                aChild = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter);
                if (aChild.childIndex >= modelIndex) {
                    if (isChildVisible) {
                        adjustRowBy(-1, counter);
                        FixedHeightLayoutCache.access$400(this$0, -1);
                    }
                    for (; counter < maxCounter; counter++) ((FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter)).childIndex--;
                    childCount--;
                    return;
                }
            }
            if (isChildVisible) {
                adjustRowBy(-1, maxCounter);
                FixedHeightLayoutCache.access$400(this$0, -1);
            }
            childCount--;
        }
    }
    
    protected void adjustChildIndexs(int index, int amount) {
        for (int counter = index, maxCounter = getChildCount(); counter < maxCounter; counter++) {
            ((FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter)).childIndex += amount;
        }
    }
    
    protected void childInsertedAtModelIndex(int index, boolean isExpandedAndVisible) {
        FixedHeightLayoutCache$FHTreeStateNode aChild;
        int maxCounter = getChildCount();
        for (int counter = 0; counter < maxCounter; counter++) {
            aChild = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter);
            if (aChild.childIndex >= index) {
                if (isExpandedAndVisible) {
                    adjustRowBy(1, counter);
                    FixedHeightLayoutCache.access$400(this$0, 1);
                }
                for (; counter < maxCounter; counter++) ((FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter)).childIndex++;
                childCount++;
                return;
            }
        }
        if (isExpandedAndVisible) {
            adjustRowBy(1, maxCounter);
            FixedHeightLayoutCache.access$400(this$0, 1);
        }
        childCount++;
    }
    
    protected boolean getPathForRow(int row, int nextRow, FixedHeightLayoutCache$SearchInfo info) {
        if (this.row == row) {
            info.node = this;
            info.isNodeParentNode = false;
            info.childIndex = childIndex;
            return true;
        }
        FixedHeightLayoutCache$FHTreeStateNode child;
        FixedHeightLayoutCache$FHTreeStateNode lastChild = null;
        for (int counter = 0, maxCounter = getChildCount(); counter < maxCounter; counter++) {
            child = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter);
            if (child.row > row) {
                if (counter == 0) {
                    info.node = this;
                    info.isNodeParentNode = true;
                    info.childIndex = row - this.row - 1;
                    return true;
                } else {
                    int lastChildEndRow = 1 + child.row - (child.childIndex - lastChild.childIndex);
                    if (row < lastChildEndRow) {
                        return lastChild.getPathForRow(row, lastChildEndRow, info);
                    }
                    info.node = this;
                    info.isNodeParentNode = true;
                    info.childIndex = row - lastChildEndRow + lastChild.childIndex + 1;
                    return true;
                }
            }
            lastChild = child;
        }
        if (lastChild != null) {
            int lastChildEndRow = nextRow - (childCount - lastChild.childIndex) + 1;
            if (row < lastChildEndRow) {
                return lastChild.getPathForRow(row, lastChildEndRow, info);
            }
            info.node = this;
            info.isNodeParentNode = true;
            info.childIndex = row - lastChildEndRow + lastChild.childIndex + 1;
            return true;
        } else {
            int retChildIndex = row - this.row - 1;
            if (retChildIndex >= childCount) {
                return false;
            }
            info.node = this;
            info.isNodeParentNode = true;
            info.childIndex = retChildIndex;
            return true;
        }
    }
    
    protected int getCountTo(int stopIndex) {
        FixedHeightLayoutCache$FHTreeStateNode aChild;
        int retCount = stopIndex + 1;
        for (int counter = 0, maxCounter = getChildCount(); counter < maxCounter; counter++) {
            aChild = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter);
            if (aChild.childIndex >= stopIndex) counter = maxCounter; else retCount += aChild.getTotalChildCount();
        }
        if (parent != null) return retCount + ((FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getParent()).getCountTo(childIndex);
        if (!this$0.isRootVisible()) return (retCount - 1);
        return retCount;
    }
    
    protected int getNumExpandedChildrenTo(int stopIndex) {
        FixedHeightLayoutCache$FHTreeStateNode aChild;
        int retCount = stopIndex;
        for (int counter = 0, maxCounter = getChildCount(); counter < maxCounter; counter++) {
            aChild = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)getChildAt(counter);
            if (aChild.childIndex >= stopIndex) return retCount; else {
                retCount += aChild.getTotalChildCount();
            }
        }
        return retCount;
    }
    
    protected void didAdjustTree() {
    }
}
