package java.awt.image;

public interface TileObserver {
    
    public void tileUpdate(WritableRenderedImage source, int tileX, int tileY, boolean willBeWritable);
}
