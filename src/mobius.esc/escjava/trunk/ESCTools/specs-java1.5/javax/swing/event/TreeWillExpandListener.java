package javax.swing.event;

import java.util.EventListener;
import javax.swing.tree.ExpandVetoException;

public interface TreeWillExpandListener extends EventListener {
    
    public void treeWillExpand(TreeExpansionEvent event) throws ExpandVetoException;
    
    public void treeWillCollapse(TreeExpansionEvent event) throws ExpandVetoException;
}
