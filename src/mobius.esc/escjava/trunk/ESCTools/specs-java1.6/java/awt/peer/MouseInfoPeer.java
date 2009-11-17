package java.awt.peer;

import java.awt.Window;
import java.awt.Point;

public interface MouseInfoPeer {
    
    int fillPointWithCoords(Point point);
    
    boolean isWindowUnderMouse(Window w);
}
