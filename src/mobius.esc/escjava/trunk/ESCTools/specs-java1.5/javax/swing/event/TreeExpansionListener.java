package javax.swing.event;

import java.util.EventListener;

public interface TreeExpansionListener extends EventListener {
    
    public void treeExpanded(TreeExpansionEvent event);
    
    public void treeCollapsed(TreeExpansionEvent event);
}
