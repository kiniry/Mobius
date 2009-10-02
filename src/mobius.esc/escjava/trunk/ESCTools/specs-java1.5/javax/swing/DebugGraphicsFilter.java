package javax.swing;

import java.awt.*;
import java.awt.image.*;

class DebugGraphicsFilter extends RGBImageFilter {
    Color color;
    
    DebugGraphicsFilter(Color c) {
        
        canFilterIndexColorModel = true;
        color = c;
    }
    
    public int filterRGB(int x, int y, int rgb) {
        return color.getRGB() | (rgb & -16777216);
    }
}
