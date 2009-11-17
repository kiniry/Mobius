package java.awt;

import java.util.Map;
import java.util.Set;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import sun.awt.SunHints;

public class RenderingHints implements Map, Cloneable {
    {
    }
    HashMap hintmap = new HashMap(7);
    public static final RenderingHints$Key KEY_ANTIALIASING = SunHints.KEY_ANTIALIASING;
    public static final Object VALUE_ANTIALIAS_ON = SunHints.VALUE_ANTIALIAS_ON;
    public static final Object VALUE_ANTIALIAS_OFF = SunHints.VALUE_ANTIALIAS_OFF;
    public static final Object VALUE_ANTIALIAS_DEFAULT = SunHints.VALUE_ANTIALIAS_DEFAULT;
    public static final RenderingHints$Key KEY_RENDERING = SunHints.KEY_RENDERING;
    public static final Object VALUE_RENDER_SPEED = SunHints.VALUE_RENDER_SPEED;
    public static final Object VALUE_RENDER_QUALITY = SunHints.VALUE_RENDER_QUALITY;
    public static final Object VALUE_RENDER_DEFAULT = SunHints.VALUE_RENDER_DEFAULT;
    public static final RenderingHints$Key KEY_DITHERING = SunHints.KEY_DITHERING;
    public static final Object VALUE_DITHER_DISABLE = SunHints.VALUE_DITHER_DISABLE;
    public static final Object VALUE_DITHER_ENABLE = SunHints.VALUE_DITHER_ENABLE;
    public static final Object VALUE_DITHER_DEFAULT = SunHints.VALUE_DITHER_DEFAULT;
    public static final RenderingHints$Key KEY_TEXT_ANTIALIASING = SunHints.KEY_TEXT_ANTIALIASING;
    public static final Object VALUE_TEXT_ANTIALIAS_ON = SunHints.VALUE_TEXT_ANTIALIAS_ON;
    public static final Object VALUE_TEXT_ANTIALIAS_OFF = SunHints.VALUE_TEXT_ANTIALIAS_OFF;
    public static final Object VALUE_TEXT_ANTIALIAS_DEFAULT = SunHints.VALUE_TEXT_ANTIALIAS_DEFAULT;
    public static final RenderingHints$Key KEY_FRACTIONALMETRICS = SunHints.KEY_FRACTIONALMETRICS;
    public static final Object VALUE_FRACTIONALMETRICS_OFF = SunHints.VALUE_FRACTIONALMETRICS_OFF;
    public static final Object VALUE_FRACTIONALMETRICS_ON = SunHints.VALUE_FRACTIONALMETRICS_ON;
    public static final Object VALUE_FRACTIONALMETRICS_DEFAULT = SunHints.VALUE_FRACTIONALMETRICS_DEFAULT;
    public static final RenderingHints$Key KEY_INTERPOLATION = SunHints.KEY_INTERPOLATION;
    public static final Object VALUE_INTERPOLATION_NEAREST_NEIGHBOR = SunHints.VALUE_INTERPOLATION_NEAREST_NEIGHBOR;
    public static final Object VALUE_INTERPOLATION_BILINEAR = SunHints.VALUE_INTERPOLATION_BILINEAR;
    public static final Object VALUE_INTERPOLATION_BICUBIC = SunHints.VALUE_INTERPOLATION_BICUBIC;
    public static final RenderingHints$Key KEY_ALPHA_INTERPOLATION = SunHints.KEY_ALPHA_INTERPOLATION;
    public static final Object VALUE_ALPHA_INTERPOLATION_SPEED = SunHints.VALUE_ALPHA_INTERPOLATION_SPEED;
    public static final Object VALUE_ALPHA_INTERPOLATION_QUALITY = SunHints.VALUE_ALPHA_INTERPOLATION_QUALITY;
    public static final Object VALUE_ALPHA_INTERPOLATION_DEFAULT = SunHints.VALUE_ALPHA_INTERPOLATION_DEFAULT;
    public static final RenderingHints$Key KEY_COLOR_RENDERING = SunHints.KEY_COLOR_RENDERING;
    public static final Object VALUE_COLOR_RENDER_SPEED = SunHints.VALUE_COLOR_RENDER_SPEED;
    public static final Object VALUE_COLOR_RENDER_QUALITY = SunHints.VALUE_COLOR_RENDER_QUALITY;
    public static final Object VALUE_COLOR_RENDER_DEFAULT = SunHints.VALUE_COLOR_RENDER_DEFAULT;
    public static final RenderingHints$Key KEY_STROKE_CONTROL = SunHints.KEY_STROKE_CONTROL;
    public static final Object VALUE_STROKE_DEFAULT = SunHints.VALUE_STROKE_DEFAULT;
    public static final Object VALUE_STROKE_NORMALIZE = SunHints.VALUE_STROKE_NORMALIZE;
    public static final Object VALUE_STROKE_PURE = SunHints.VALUE_STROKE_PURE;
    
    public RenderingHints(Map init) {
        
        if (init != null) {
            hintmap.putAll(init);
        }
    }
    
    public RenderingHints(RenderingHints$Key key, Object value) {
        
        hintmap.put(key, value);
    }
    
    public int size() {
        return hintmap.size();
    }
    
    public boolean isEmpty() {
        return hintmap.isEmpty();
    }
    
    public boolean containsKey(Object key) {
        return hintmap.containsKey((RenderingHints$Key)(RenderingHints$Key)key);
    }
    
    public boolean containsValue(Object value) {
        return hintmap.containsValue(value);
    }
    
    public Object get(Object key) {
        return hintmap.get((RenderingHints$Key)(RenderingHints$Key)key);
    }
    
    public Object put(Object key, Object value) {
        if (!((RenderingHints$Key)(RenderingHints$Key)key).isCompatibleValue(value)) {
            throw new IllegalArgumentException(value + " incompatible with " + key);
        }
        return hintmap.put((RenderingHints$Key)(RenderingHints$Key)key, value);
    }
    
    public void add(RenderingHints hints) {
        hintmap.putAll(hints.hintmap);
    }
    
    public void clear() {
        hintmap.clear();
    }
    
    public Object remove(Object key) {
        return hintmap.remove((RenderingHints$Key)(RenderingHints$Key)key);
    }
    
    public void putAll(Map m) {
        if (RenderingHints.class.isInstance(m)) {
            for (Iterator i$ = m.entrySet().iterator(); i$.hasNext(); ) {
                Map$Entry entry = (Map$Entry)i$.next();
                hintmap.put(entry.getKey(), entry.getValue());
            }
        } else {
            for (Iterator i$ = m.entrySet().iterator(); i$.hasNext(); ) {
                Map$Entry entry = (Map$Entry)i$.next();
                put(entry.getKey(), entry.getValue());
            }
        }
    }
    
    public Set keySet() {
        return hintmap.keySet();
    }
    
    public Collection values() {
        return hintmap.values();
    }
    
    public Set entrySet() {
        return Collections.unmodifiableMap(hintmap).entrySet();
    }
    
    public boolean equals(Object o) {
        if (o instanceof RenderingHints) {
            return hintmap.equals(((RenderingHints)(RenderingHints)o).hintmap);
        } else if (o instanceof Map) {
            return hintmap.equals(o);
        }
        return false;
    }
    
    public int hashCode() {
        return hintmap.hashCode();
    }
    
    public Object clone() {
        RenderingHints rh;
        try {
            rh = (RenderingHints)(RenderingHints)super.clone();
            if (hintmap != null) {
                rh.hintmap = (HashMap)(HashMap)hintmap.clone();
            }
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
        return rh;
    }
    
    public String toString() {
        if (hintmap == null) {
            return getClass().getName() + "@" + Integer.toHexString(hashCode()) + " (0 hints)";
        }
        return hintmap.toString();
    }
}
