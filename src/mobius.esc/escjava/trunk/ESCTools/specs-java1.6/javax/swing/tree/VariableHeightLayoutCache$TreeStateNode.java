package javax.swing.tree;

import java.awt.Rectangle;
import java.util.Enumeration;

class VariableHeightLayoutCache$TreeStateNode extends DefaultMutableTreeNode {
    /*synthetic*/ final VariableHeightLayoutCache this$0;
    protected int preferredWidth;
    protected int preferredHeight;
    protected int xOrigin;
    protected int yOrigin;
    protected boolean expanded;
    protected boolean hasBeenExpanded;
    protected TreePath path;
    
    public VariableHeightLayoutCache$TreeStateNode(/*synthetic*/ final VariableHeightLayoutCache this$0, Object value) {
        super(value);
        this.this$0 = this$0;
    }
    
    public void setParent(MutableTreeNode parent) {
        super.setParent(parent);
        if (parent != null) {
            path = ((VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)parent).getTreePath().pathByAddingChild(getUserObject());
            VariableHeightLayoutCache.access$000(this$0, this);
        }
    }
    
    public void remove(int childIndex) {
        VariableHeightLayoutCache$TreeStateNode node = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)getChildAt(childIndex);
        node.removeFromMapping();
        super.remove(childIndex);
    }
    
    public void setUserObject(Object o) {
        super.setUserObject(o);
        if (path != null) {
            VariableHeightLayoutCache$TreeStateNode parent = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)getParent();
            if (parent != null) resetChildrenPaths(parent.getTreePath()); else resetChildrenPaths(null);
        }
    }
    
    public Enumeration children() {
        if (!this.isExpanded()) {
            return DefaultMutableTreeNode.EMPTY_ENUMERATION;
        } else {
            return super.children();
        }
    }
    
    public boolean isLeaf() {
        return this$0.getModel().isLeaf(this.getValue());
    }
    
    public Rectangle getNodeBounds(Rectangle placeIn) {
        if (placeIn == null) placeIn = new Rectangle(getXOrigin(), getYOrigin(), getPreferredWidth(), getPreferredHeight()); else {
            placeIn.x = getXOrigin();
            placeIn.y = getYOrigin();
            placeIn.width = getPreferredWidth();
            placeIn.height = getPreferredHeight();
        }
        return placeIn;
    }
    
    public int getXOrigin() {
        if (!hasValidSize()) updatePreferredSize(getRow());
        return xOrigin;
    }
    
    public int getYOrigin() {
        if (this$0.isFixedRowHeight()) {
            int aRow = getRow();
            if (aRow == -1) return -1;
            return this$0.getRowHeight() * aRow;
        }
        return yOrigin;
    }
    
    public int getPreferredHeight() {
        if (this$0.isFixedRowHeight()) return this$0.getRowHeight(); else if (!hasValidSize()) updatePreferredSize(getRow());
        return preferredHeight;
    }
    
    public int getPreferredWidth() {
        if (!hasValidSize()) updatePreferredSize(getRow());
        return preferredWidth;
    }
    
    public boolean hasValidSize() {
        return (preferredHeight != 0);
    }
    
    public int getRow() {
        return VariableHeightLayoutCache.access$100(this$0).indexOf(this);
    }
    
    public boolean hasBeenExpanded() {
        return hasBeenExpanded;
    }
    
    public boolean isExpanded() {
        return expanded;
    }
    
    public VariableHeightLayoutCache$TreeStateNode getLastVisibleNode() {
        VariableHeightLayoutCache$TreeStateNode node = this;
        while (node.isExpanded() && node.getChildCount() > 0) node = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)node.getLastChild();
        return node;
    }
    
    public boolean isVisible() {
        if (this == VariableHeightLayoutCache.access$200(this$0)) return true;
        VariableHeightLayoutCache$TreeStateNode parent = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)getParent();
        return (parent != null && parent.isExpanded() && parent.isVisible());
    }
    
    public int getModelChildCount() {
        if (hasBeenExpanded) return super.getChildCount();
        return this$0.getModel().getChildCount(getValue());
    }
    
    public int getVisibleChildCount() {
        int childCount = 0;
        if (isExpanded()) {
            int maxCounter = getChildCount();
            childCount += maxCounter;
            for (int counter = 0; counter < maxCounter; counter++) childCount += ((VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)getChildAt(counter)).getVisibleChildCount();
        }
        return childCount;
    }
    
    public void toggleExpanded() {
        if (isExpanded()) {
            collapse();
        } else {
            expand();
        }
    }
    
    public void makeVisible() {
        VariableHeightLayoutCache$TreeStateNode parent = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)getParent();
        if (parent != null) parent.expandParentAndReceiver();
    }
    
    public void expand() {
        expand(true);
    }
    
    public void collapse() {
        collapse(true);
    }
    
    public Object getValue() {
        return getUserObject();
    }
    
    public TreePath getTreePath() {
        return path;
    }
    
    protected void resetChildrenPaths(TreePath parentPath) {
        VariableHeightLayoutCache.access$300(this$0, this);
        if (parentPath == null) path = new TreePath(getUserObject()); else path = parentPath.pathByAddingChild(getUserObject());
        VariableHeightLayoutCache.access$000(this$0, this);
        for (int counter = getChildCount() - 1; counter >= 0; counter--) ((VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)getChildAt(counter)).resetChildrenPaths(path);
    }
    
    protected void setYOrigin(int newYOrigin) {
        yOrigin = newYOrigin;
    }
    
    protected void shiftYOriginBy(int offset) {
        yOrigin += offset;
    }
    
    protected void updatePreferredSize() {
        updatePreferredSize(getRow());
    }
    
    protected void updatePreferredSize(int index) {
        Rectangle bounds = this$0.getNodeDimensions(this.getUserObject(), index, getLevel(), isExpanded(), VariableHeightLayoutCache.access$400(this$0));
        if (bounds == null) {
            xOrigin = 0;
            preferredWidth = preferredHeight = 0;
            VariableHeightLayoutCache.access$502(this$0, true);
        } else if (bounds.height == 0) {
            xOrigin = 0;
            preferredWidth = preferredHeight = 0;
            VariableHeightLayoutCache.access$502(this$0, true);
        } else {
            xOrigin = bounds.x;
            preferredWidth = bounds.width;
            if (this$0.isFixedRowHeight()) preferredHeight = this$0.getRowHeight(); else preferredHeight = bounds.height;
        }
    }
    
    protected void markSizeInvalid() {
        preferredHeight = 0;
    }
    
    protected void deepMarkSizeInvalid() {
        markSizeInvalid();
        for (int counter = getChildCount() - 1; counter >= 0; counter--) ((VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)getChildAt(counter)).deepMarkSizeInvalid();
    }
    
    protected Enumeration getLoadedChildren(boolean createIfNeeded) {
        if (!createIfNeeded || hasBeenExpanded) return super.children();
        VariableHeightLayoutCache$TreeStateNode newNode;
        Object realNode = getValue();
        TreeModel treeModel = this$0.getModel();
        int count = treeModel.getChildCount(realNode);
        hasBeenExpanded = true;
        int childRow = getRow();
        if (childRow == -1) {
            for (int i = 0; i < count; i++) {
                newNode = VariableHeightLayoutCache.access$600(this$0, treeModel.getChild(realNode, i));
                this.add(newNode);
                newNode.updatePreferredSize(-1);
            }
        } else {
            childRow++;
            for (int i = 0; i < count; i++) {
                newNode = VariableHeightLayoutCache.access$600(this$0, treeModel.getChild(realNode, i));
                this.add(newNode);
                newNode.updatePreferredSize(childRow++);
            }
        }
        return super.children();
    }
    
    protected void didAdjustTree() {
    }
    
    protected void expandParentAndReceiver() {
        VariableHeightLayoutCache$TreeStateNode parent = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)getParent();
        if (parent != null) parent.expandParentAndReceiver();
        expand();
    }
    
    protected void expand(boolean adjustTree) {
        if (!isExpanded() && !isLeaf()) {
            boolean isFixed = this$0.isFixedRowHeight();
            int startHeight = getPreferredHeight();
            int originalRow = getRow();
            expanded = true;
            updatePreferredSize(originalRow);
            if (!hasBeenExpanded) {
                VariableHeightLayoutCache$TreeStateNode newNode;
                Object realNode = getValue();
                TreeModel treeModel = this$0.getModel();
                int count = treeModel.getChildCount(realNode);
                hasBeenExpanded = true;
                if (originalRow == -1) {
                    for (int i = 0; i < count; i++) {
                        newNode = VariableHeightLayoutCache.access$600(this$0, treeModel.getChild(realNode, i));
                        this.add(newNode);
                        newNode.updatePreferredSize(-1);
                    }
                } else {
                    int offset = originalRow + 1;
                    for (int i = 0; i < count; i++) {
                        newNode = VariableHeightLayoutCache.access$600(this$0, treeModel.getChild(realNode, i));
                        this.add(newNode);
                        newNode.updatePreferredSize(offset);
                    }
                }
            }
            int i = originalRow;
            Enumeration cursor = preorderEnumeration();
            cursor.nextElement();
            int newYOrigin;
            if (isFixed) newYOrigin = 0; else if (this == VariableHeightLayoutCache.access$200(this$0) && !this$0.isRootVisible()) newYOrigin = 0; else newYOrigin = getYOrigin() + this.getPreferredHeight();
            VariableHeightLayoutCache$TreeStateNode aNode;
            if (!isFixed) {
                while (cursor.hasMoreElements()) {
                    aNode = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)cursor.nextElement();
                    if (!VariableHeightLayoutCache.access$500(this$0) && !aNode.hasValidSize()) aNode.updatePreferredSize(i + 1);
                    aNode.setYOrigin(newYOrigin);
                    newYOrigin += aNode.getPreferredHeight();
                    VariableHeightLayoutCache.access$100(this$0).insertElementAt(aNode, ++i);
                }
            } else {
                while (cursor.hasMoreElements()) {
                    aNode = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)cursor.nextElement();
                    VariableHeightLayoutCache.access$100(this$0).insertElementAt(aNode, ++i);
                }
            }
            if (adjustTree && (originalRow != i || getPreferredHeight() != startHeight)) {
                if (!isFixed && ++i < this$0.getRowCount()) {
                    int counter;
                    int heightDiff = newYOrigin - (getYOrigin() + getPreferredHeight()) + (getPreferredHeight() - startHeight);
                    for (counter = VariableHeightLayoutCache.access$100(this$0).size() - 1; counter >= i; counter--) ((VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)VariableHeightLayoutCache.access$100(this$0).elementAt(counter)).shiftYOriginBy(heightDiff);
                }
                didAdjustTree();
                VariableHeightLayoutCache.access$700(this$0);
            }
            if (this$0.treeSelectionModel != null) {
                this$0.treeSelectionModel.resetRowSelection();
            }
        }
    }
    
    protected void collapse(boolean adjustTree) {
        if (isExpanded()) {
            Enumeration cursor = preorderEnumeration();
            cursor.nextElement();
            int rowsDeleted = 0;
            boolean isFixed = this$0.isFixedRowHeight();
            int lastYEnd;
            if (isFixed) lastYEnd = 0; else lastYEnd = getPreferredHeight() + getYOrigin();
            int startHeight = getPreferredHeight();
            int startYEnd = lastYEnd;
            int myRow = getRow();
            if (!isFixed) {
                while (cursor.hasMoreElements()) {
                    VariableHeightLayoutCache$TreeStateNode node = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)cursor.nextElement();
                    if (node.isVisible()) {
                        rowsDeleted++;
                        lastYEnd = node.getYOrigin() + node.getPreferredHeight();
                    }
                }
            } else {
                while (cursor.hasMoreElements()) {
                    VariableHeightLayoutCache$TreeStateNode node = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)cursor.nextElement();
                    if (node.isVisible()) {
                        rowsDeleted++;
                    }
                }
            }
            for (int counter = rowsDeleted + myRow; counter > myRow; counter--) {
                VariableHeightLayoutCache.access$100(this$0).removeElementAt(counter);
            }
            expanded = false;
            if (myRow == -1) markSizeInvalid(); else if (adjustTree) updatePreferredSize(myRow);
            if (myRow != -1 && adjustTree && (rowsDeleted > 0 || startHeight != getPreferredHeight())) {
                startYEnd += (getPreferredHeight() - startHeight);
                if (!isFixed && (myRow + 1) < this$0.getRowCount() && startYEnd != lastYEnd) {
                    int counter;
                    int maxCounter;
                    int shiftAmount;
                    shiftAmount = startYEnd - lastYEnd;
                    for (counter = myRow + 1, maxCounter = VariableHeightLayoutCache.access$100(this$0).size(); counter < maxCounter; counter++) ((VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)VariableHeightLayoutCache.access$100(this$0).elementAt(counter)).shiftYOriginBy(shiftAmount);
                }
                didAdjustTree();
                VariableHeightLayoutCache.access$700(this$0);
            }
            if (this$0.treeSelectionModel != null && rowsDeleted > 0 && myRow != -1) {
                this$0.treeSelectionModel.resetRowSelection();
            }
        }
    }
    
    protected void removeFromMapping() {
        if (path != null) {
            VariableHeightLayoutCache.access$300(this$0, this);
            for (int counter = getChildCount() - 1; counter >= 0; counter--) ((VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)getChildAt(counter)).removeFromMapping();
        }
    }
}
