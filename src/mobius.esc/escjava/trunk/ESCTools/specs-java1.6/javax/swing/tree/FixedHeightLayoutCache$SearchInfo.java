package javax.swing.tree;

class FixedHeightLayoutCache$SearchInfo {
    
    /*synthetic*/ FixedHeightLayoutCache$SearchInfo(FixedHeightLayoutCache x0, javax.swing.tree.FixedHeightLayoutCache$1 x1) {
        this(x0);
    }
    /*synthetic*/ final FixedHeightLayoutCache this$0;
    
    private FixedHeightLayoutCache$SearchInfo(/*synthetic*/ final FixedHeightLayoutCache this$0) {
        this.this$0 = this$0;
        
    }
    protected FixedHeightLayoutCache$FHTreeStateNode node;
    protected boolean isNodeParentNode;
    protected int childIndex;
    
    protected TreePath getPath() {
        if (node == null) return null;
        if (isNodeParentNode) return node.getTreePath().pathByAddingChild(this$0.treeModel.getChild(node.getUserObject(), childIndex));
        return node.path;
    }
}
