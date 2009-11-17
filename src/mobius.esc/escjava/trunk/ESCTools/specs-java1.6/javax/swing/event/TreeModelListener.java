package javax.swing.event;

import java.util.EventListener;

public interface TreeModelListener extends EventListener {
    
    void treeNodesChanged(TreeModelEvent e);
    
    void treeNodesInserted(TreeModelEvent e);
    
    void treeNodesRemoved(TreeModelEvent e);
    
    void treeStructureChanged(TreeModelEvent e);
}
