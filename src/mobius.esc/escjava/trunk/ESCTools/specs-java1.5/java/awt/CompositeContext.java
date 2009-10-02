package java.awt;

import java.awt.image.Raster;
import java.awt.image.WritableRaster;

public interface CompositeContext {
    
    public void dispose();
    
    public void compose(Raster src, Raster dstIn, WritableRaster dstOut);
}
