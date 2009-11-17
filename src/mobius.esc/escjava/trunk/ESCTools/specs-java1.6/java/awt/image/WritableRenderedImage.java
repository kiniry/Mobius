package java.awt.image;

import java.awt.Point;

public interface WritableRenderedImage extends RenderedImage {
    
    public void addTileObserver(TileObserver to);
    
    public void removeTileObserver(TileObserver to);
    
    public WritableRaster getWritableTile(int tileX, int tileY);
    
    public void releaseWritableTile(int tileX, int tileY);
    
    public boolean isTileWritable(int tileX, int tileY);
    
    public Point[] getWritableTileIndices();
    
    public boolean hasTileWriters();
    
    public void setData(Raster r);
}
