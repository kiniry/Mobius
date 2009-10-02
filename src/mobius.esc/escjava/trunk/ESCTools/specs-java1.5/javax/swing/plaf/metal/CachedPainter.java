package javax.swing.plaf.metal;

import java.awt.*;
import java.awt.image.*;
import java.util.*;

abstract class CachedPainter {
    private static final Map cacheMap = new HashMap();
    
    private static CachedPainter$Cache getCache(Object key) {
        synchronized (cacheMap) {
            CachedPainter$Cache cache = (CachedPainter$Cache)cacheMap.get(key);
            if (cache == null) {
                cache = new CachedPainter$Cache(1);
                cacheMap.put(key, cache);
            }
            return cache;
        }
    }
    
    public CachedPainter(int cacheCount) {
        
        getCache(getClass()).setMaxCount(cacheCount);
    }
    
    protected void paint(Component c, Graphics g, int x, int y, int w, int h, Object... args) {
        if (w <= 0 || h <= 0) {
            return;
        }
        Object key = getClass();
        GraphicsConfiguration config = c.getGraphicsConfiguration();
        CachedPainter$Cache cache = getCache(key);
        Image image = cache.getImage(key, config, w, h, args);
        int attempts = 0;
        do {
            boolean draw = false;
            if (image instanceof VolatileImage) {
                switch (((VolatileImage)(VolatileImage)image).validate(config)) {
                case VolatileImage.IMAGE_INCOMPATIBLE: 
                    ((VolatileImage)(VolatileImage)image).flush();
                    image = null;
                    break;
                
                case VolatileImage.IMAGE_RESTORED: 
                    draw = true;
                    break;
                
                }
            }
            if (image == null) {
                image = createImage(c, w, h, config);
                cache.setImage(key, config, w, h, args, image);
                draw = true;
            }
            if (draw) {
                Graphics g2 = image.getGraphics();
                paintToImage(c, g2, w, h, args);
                g2.dispose();
            }
            paintImage(c, g, x, y, w, h, image, args);
        }         while ((image instanceof VolatileImage) && ((VolatileImage)(VolatileImage)image).contentsLost() && ++attempts < 3);
    }
    
    protected abstract void paintToImage(Component c, Graphics g, int w, int h, Object[] args);
    
    protected void paintImage(Component c, Graphics g, int x, int y, int w, int h, Image image, Object[] args) {
        g.drawImage(image, x, y, null);
    }
    
    protected Image createImage(Component c, int w, int h, GraphicsConfiguration config) {
        if (config == null) {
            return new BufferedImage(w, h, BufferedImage.TYPE_INT_RGB);
        }
        return config.createCompatibleVolatileImage(w, h);
    }
    {
    }
}
