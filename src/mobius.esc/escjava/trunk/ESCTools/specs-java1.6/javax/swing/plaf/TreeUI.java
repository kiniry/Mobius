package javax.swing.plaf;

import java.awt.Rectangle;
import javax.swing.JTree;
import javax.swing.tree.TreePath;

public abstract class TreeUI extends ComponentUI {
    
    public TreeUI() {
        
    }
    
    public abstract Rectangle getPathBounds(JTree tree, TreePath path);
    
    public abstract TreePath getPathForRow(JTree tree, int row);
    
    public abstract int getRowForPath(JTree tree, TreePath path);
    
    public abstract int getRowCount(JTree tree);
    
    public abstract TreePath getClosestPathForLocation(JTree tree, int x, int y);
    
    public abstract boolean isEditing(JTree tree);
    
    public abstract boolean stopEditing(JTree tree);
    
    public abstract void cancelEditing(JTree tree);
    
    public abstract void startEditingAtPath(JTree tree, TreePath path);
    
    public abstract TreePath getEditingPath(JTree tree);
}
