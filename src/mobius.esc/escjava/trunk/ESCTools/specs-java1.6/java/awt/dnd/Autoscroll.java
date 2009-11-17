package java.awt.dnd;

import java.awt.Insets;
import java.awt.Point;

public interface Autoscroll {
    
    public Insets getAutoscrollInsets();
    
    public void autoscroll(Point cursorLocn);
}
