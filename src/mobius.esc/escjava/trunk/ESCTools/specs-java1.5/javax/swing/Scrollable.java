package javax.swing;

import java.awt.Dimension;
import java.awt.Rectangle;

public interface Scrollable {
    
    Dimension getPreferredScrollableViewportSize();
    
    int getScrollableUnitIncrement(Rectangle visibleRect, int orientation, int direction);
    
    int getScrollableBlockIncrement(Rectangle visibleRect, int orientation, int direction);
    
    boolean getScrollableTracksViewportWidth();
    
    boolean getScrollableTracksViewportHeight();
}
