package javax.swing.plaf.metal;

import java.awt.*;
import java.awt.image.*;
import java.lang.ref.SoftReference;
import java.util.*;

class CachedPainter$Cache {
    private int maxCount;
    private java.util.List entries;
    
    CachedPainter$Cache(int maxCount) {
        
        this.maxCount = maxCount;
        entries = new ArrayList(maxCount);
    }
    
    void setMaxCount(int maxCount) {
        this.maxCount = maxCount;
    }
    
    private CachedPainter$Cache$Entry getEntry(Object key, GraphicsConfiguration config, int w, int h, Object[] args) {
        synchronized (this) {
            CachedPainter$Cache$Entry entry;
            for (int counter = entries.size() - 1; counter >= 0; counter--) {
                entry = (CachedPainter$Cache$Entry)((SoftReference)entries.get(counter)).get();
                if (entry == null) {
                    entries.remove(counter);
                } else if (entry.equals(config, w, h, args)) {
                    return entry;
                }
            }
            entry = new CachedPainter$Cache$Entry(config, w, h, args);
            if (entries.size() == maxCount) {
                entries.remove(0);
            }
            entries.add(new SoftReference(entry));
            return entry;
        }
    }
    
    public Image getImage(Object key, GraphicsConfiguration config, int w, int h, Object[] args) {
        CachedPainter$Cache$Entry entry = getEntry(key, config, w, h, args);
        return entry.getImage();
    }
    
    public void setImage(Object key, GraphicsConfiguration config, int w, int h, Object[] args, Image image) {
        CachedPainter$Cache$Entry entry = getEntry(key, config, w, h, args);
        entry.setImage(image);
    }
    {
    }
}
