package java.beans;

class javax_swing_tree_DefaultMutableTreeNode_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    javax_swing_tree_DefaultMutableTreeNode_PersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        super.initialize(type, oldInstance, newInstance, out);
        javax.swing.tree.DefaultMutableTreeNode m = (javax.swing.tree.DefaultMutableTreeNode)(javax.swing.tree.DefaultMutableTreeNode)oldInstance;
        javax.swing.tree.DefaultMutableTreeNode n = (javax.swing.tree.DefaultMutableTreeNode)(javax.swing.tree.DefaultMutableTreeNode)newInstance;
        for (int i = n.getChildCount(); i < m.getChildCount(); i++) {
            invokeStatement(oldInstance, "add", new Object[]{m.getChildAt(i)}, out);
        }
    }
}
