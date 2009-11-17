package javax.swing.plaf;

import javax.swing.JList;
import java.awt.Point;
import java.awt.Rectangle;

public abstract class ListUI extends ComponentUI {
    
    public ListUI() {
        
    }
    
    public abstract int locationToIndex(JList list, Point location);
    
    public abstract Point indexToLocation(JList list, int index);
    
    public abstract Rectangle getCellBounds(JList list, int index1, int index2);
}
