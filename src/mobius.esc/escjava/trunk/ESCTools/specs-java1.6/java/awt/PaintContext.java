package java.awt;

import java.awt.image.Raster;
import java.awt.image.ColorModel;

public interface PaintContext {
    
    public void dispose();
    
    ColorModel getColorModel();
    
    Raster getRaster(int x, int y, int w, int h);
}
