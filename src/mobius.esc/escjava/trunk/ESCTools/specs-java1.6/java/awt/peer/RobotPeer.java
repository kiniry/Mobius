package java.awt.peer;

import java.awt.*;

public interface RobotPeer {
    
    public void mouseMove(int x, int y);
    
    public void mousePress(int buttons);
    
    public void mouseRelease(int buttons);
    
    public void mouseWheel(int wheelAmt);
    
    public void keyPress(int keycode);
    
    public void keyRelease(int keycode);
    
    public int getRGBPixel(int x, int y);
    
    public int[] getRGBPixels(Rectangle bounds);
}
