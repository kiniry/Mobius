package java.awt;

import java.io.*;
import java.lang.*;
import java.awt.image.ColorModel;
import java.awt.geom.AffineTransform;
import java.awt.geom.Rectangle2D;
import java.awt.color.ColorSpace;

public class Color implements Paint, java.io.Serializable {
    public static final Color white = new Color(255, 255, 255);
    public static final Color WHITE = white;
    public static final Color lightGray = new Color(192, 192, 192);
    public static final Color LIGHT_GRAY = lightGray;
    public static final Color gray = new Color(128, 128, 128);
    public static final Color GRAY = gray;
    public static final Color darkGray = new Color(64, 64, 64);
    public static final Color DARK_GRAY = darkGray;
    public static final Color black = new Color(0, 0, 0);
    public static final Color BLACK = black;
    public static final Color red = new Color(255, 0, 0);
    public static final Color RED = red;
    public static final Color pink = new Color(255, 175, 175);
    public static final Color PINK = pink;
    public static final Color orange = new Color(255, 200, 0);
    public static final Color ORANGE = orange;
    public static final Color yellow = new Color(255, 255, 0);
    public static final Color YELLOW = yellow;
    public static final Color green = new Color(0, 255, 0);
    public static final Color GREEN = green;
    public static final Color magenta = new Color(255, 0, 255);
    public static final Color MAGENTA = magenta;
    public static final Color cyan = new Color(0, 255, 255);
    public static final Color CYAN = cyan;
    public static final Color blue = new Color(0, 0, 255);
    public static final Color BLUE = blue;
    private transient long pData;
    int value;
    private float[] frgbvalue = null;
    private float[] fvalue = null;
    private float falpha = 0.0F;
    private ColorSpace cs = null;
    private static final long serialVersionUID = 118526816881161077L;
    
    private static native void initIDs();
    static {
        Toolkit.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    
    private static void testColorValueRange(int r, int g, int b, int a) {
        boolean rangeError = false;
        String badComponentString = "";
        if (a < 0 || a > 255) {
            rangeError = true;
            badComponentString = badComponentString + " Alpha";
        }
        if (r < 0 || r > 255) {
            rangeError = true;
            badComponentString = badComponentString + " Red";
        }
        if (g < 0 || g > 255) {
            rangeError = true;
            badComponentString = badComponentString + " Green";
        }
        if (b < 0 || b > 255) {
            rangeError = true;
            badComponentString = badComponentString + " Blue";
        }
        if (rangeError == true) {
            throw new IllegalArgumentException("Color parameter outside of expected range:" + badComponentString);
        }
    }
    
    private static void testColorValueRange(float r, float g, float b, float a) {
        boolean rangeError = false;
        String badComponentString = "";
        if (a < 0.0 || a > 1.0) {
            rangeError = true;
            badComponentString = badComponentString + " Alpha";
        }
        if (r < 0.0 || r > 1.0) {
            rangeError = true;
            badComponentString = badComponentString + " Red";
        }
        if (g < 0.0 || g > 1.0) {
            rangeError = true;
            badComponentString = badComponentString + " Green";
        }
        if (b < 0.0 || b > 1.0) {
            rangeError = true;
            badComponentString = badComponentString + " Blue";
        }
        if (rangeError == true) {
            throw new IllegalArgumentException("Color parameter outside of expected range:" + badComponentString);
        }
    }
    
    public Color(int r, int g, int b) {
        this(r, g, b, 255);
    }
    
    public Color(int r, int g, int b, int a) {
        
        value = ((a & 255) << 24) | ((r & 255) << 16) | ((g & 255) << 8) | ((b & 255) << 0);
        testColorValueRange(r, g, b, a);
    }
    
    public Color(int rgb) {
        
        value = -16777216 | rgb;
    }
    
    public Color(int rgba, boolean hasalpha) {
        
        if (hasalpha) {
            value = rgba;
        } else {
            value = -16777216 | rgba;
        }
    }
    
    public Color(float r, float g, float b) {
        this((int)(r * 255 + 0.5), (int)(g * 255 + 0.5), (int)(b * 255 + 0.5));
        testColorValueRange(r, g, b, 1.0F);
        frgbvalue = new float[3];
        frgbvalue[0] = r;
        frgbvalue[1] = g;
        frgbvalue[2] = b;
        falpha = 1.0F;
        fvalue = frgbvalue;
    }
    
    public Color(float r, float g, float b, float a) {
        this((int)(r * 255 + 0.5), (int)(g * 255 + 0.5), (int)(b * 255 + 0.5), (int)(a * 255 + 0.5));
        frgbvalue = new float[3];
        frgbvalue[0] = r;
        frgbvalue[1] = g;
        frgbvalue[2] = b;
        falpha = a;
        fvalue = frgbvalue;
    }
    
    public Color(ColorSpace cspace, float[] components, float alpha) {
        
        boolean rangeError = false;
        String badComponentString = "";
        int n = cspace.getNumComponents();
        fvalue = new float[n];
        for (int i = 0; i < n; i++) {
            if (components[i] < 0.0 || components[i] > 1.0) {
                rangeError = true;
                badComponentString = badComponentString + "Component " + i + " ";
            } else {
                fvalue[i] = components[i];
            }
        }
        if (alpha < 0.0 || alpha > 1.0) {
            rangeError = true;
            badComponentString = badComponentString + "Alpha";
        } else {
            falpha = alpha;
        }
        if (rangeError) {
            throw new IllegalArgumentException("Color parameter outside of expected range: " + badComponentString);
        }
        frgbvalue = cspace.toRGB(fvalue);
        cs = cspace;
        value = ((((int)(falpha * 255)) & 255) << 24) | ((((int)(frgbvalue[0] * 255)) & 255) << 16) | ((((int)(frgbvalue[1] * 255)) & 255) << 8) | ((((int)(frgbvalue[2] * 255)) & 255) << 0);
    }
    
    public int getRed() {
        return (getRGB() >> 16) & 255;
    }
    
    public int getGreen() {
        return (getRGB() >> 8) & 255;
    }
    
    public int getBlue() {
        return (getRGB() >> 0) & 255;
    }
    
    public int getAlpha() {
        return (getRGB() >> 24) & 255;
    }
    
    public int getRGB() {
        return value;
    }
    private static final double FACTOR = 0.7;
    
    public Color brighter() {
        int r = getRed();
        int g = getGreen();
        int b = getBlue();
        int i = (int)(1.0 / (1.0 - FACTOR));
        if (r == 0 && g == 0 && b == 0) {
            return new Color(i, i, i);
        }
        if (r > 0 && r < i) r = i;
        if (g > 0 && g < i) g = i;
        if (b > 0 && b < i) b = i;
        return new Color(Math.min((int)(r / FACTOR), 255), Math.min((int)(g / FACTOR), 255), Math.min((int)(b / FACTOR), 255));
    }
    
    public Color darker() {
        return new Color(Math.max((int)(getRed() * FACTOR), 0), Math.max((int)(getGreen() * FACTOR), 0), Math.max((int)(getBlue() * FACTOR), 0));
    }
    
    public int hashCode() {
        return value;
    }
    
    public boolean equals(Object obj) {
        return obj instanceof Color && ((Color)(Color)obj).value == this.value;
    }
    
    public String toString() {
        return getClass().getName() + "[r=" + getRed() + ",g=" + getGreen() + ",b=" + getBlue() + "]";
    }
    
    public static Color decode(String nm) throws NumberFormatException {
        Integer intval = Integer.decode(nm);
        int i = intval.intValue();
        return new Color((i >> 16) & 255, (i >> 8) & 255, i & 255);
    }
    
    public static Color getColor(String nm) {
        return getColor(nm, null);
    }
    
    public static Color getColor(String nm, Color v) {
        Integer intval = Integer.getInteger(nm);
        if (intval == null) {
            return v;
        }
        int i = intval.intValue();
        return new Color((i >> 16) & 255, (i >> 8) & 255, i & 255);
    }
    
    public static Color getColor(String nm, int v) {
        Integer intval = Integer.getInteger(nm);
        int i = (intval != null) ? intval.intValue() : v;
        return new Color((i >> 16) & 255, (i >> 8) & 255, (i >> 0) & 255);
    }
    
    public static int HSBtoRGB(float hue, float saturation, float brightness) {
        int r = 0;
        int g = 0;
        int b = 0;
        if (saturation == 0) {
            r = g = b = (int)(brightness * 255.0F + 0.5F);
        } else {
            float h = (hue - (float)Math.floor(hue)) * 6.0F;
            float f = h - (float)java.lang.Math.floor(h);
            float p = brightness * (1.0F - saturation);
            float q = brightness * (1.0F - saturation * f);
            float t = brightness * (1.0F - (saturation * (1.0F - f)));
            switch ((int)h) {
            case 0: 
                r = (int)(brightness * 255.0F + 0.5F);
                g = (int)(t * 255.0F + 0.5F);
                b = (int)(p * 255.0F + 0.5F);
                break;
            
            case 1: 
                r = (int)(q * 255.0F + 0.5F);
                g = (int)(brightness * 255.0F + 0.5F);
                b = (int)(p * 255.0F + 0.5F);
                break;
            
            case 2: 
                r = (int)(p * 255.0F + 0.5F);
                g = (int)(brightness * 255.0F + 0.5F);
                b = (int)(t * 255.0F + 0.5F);
                break;
            
            case 3: 
                r = (int)(p * 255.0F + 0.5F);
                g = (int)(q * 255.0F + 0.5F);
                b = (int)(brightness * 255.0F + 0.5F);
                break;
            
            case 4: 
                r = (int)(t * 255.0F + 0.5F);
                g = (int)(p * 255.0F + 0.5F);
                b = (int)(brightness * 255.0F + 0.5F);
                break;
            
            case 5: 
                r = (int)(brightness * 255.0F + 0.5F);
                g = (int)(p * 255.0F + 0.5F);
                b = (int)(q * 255.0F + 0.5F);
                break;
            
            }
        }
        return -16777216 | (r << 16) | (g << 8) | (b << 0);
    }
    
    public static float[] RGBtoHSB(int r, int g, int b, float[] hsbvals) {
        float hue;
        float saturation;
        float brightness;
        if (hsbvals == null) {
            hsbvals = new float[3];
        }
        int cmax = (r > g) ? r : g;
        if (b > cmax) cmax = b;
        int cmin = (r < g) ? r : g;
        if (b < cmin) cmin = b;
        brightness = ((float)cmax) / 255.0F;
        if (cmax != 0) saturation = ((float)(cmax - cmin)) / ((float)cmax); else saturation = 0;
        if (saturation == 0) hue = 0; else {
            float redc = ((float)(cmax - r)) / ((float)(cmax - cmin));
            float greenc = ((float)(cmax - g)) / ((float)(cmax - cmin));
            float bluec = ((float)(cmax - b)) / ((float)(cmax - cmin));
            if (r == cmax) hue = bluec - greenc; else if (g == cmax) hue = 2.0F + redc - bluec; else hue = 4.0F + greenc - redc;
            hue = hue / 6.0F;
            if (hue < 0) hue = hue + 1.0F;
        }
        hsbvals[0] = hue;
        hsbvals[1] = saturation;
        hsbvals[2] = brightness;
        return hsbvals;
    }
    
    public static Color getHSBColor(float h, float s, float b) {
        return new Color(HSBtoRGB(h, s, b));
    }
    
    public float[] getRGBComponents(float[] compArray) {
        float[] f;
        if (compArray == null) {
            f = new float[4];
        } else {
            f = compArray;
        }
        if (frgbvalue == null) {
            f[0] = ((float)getRed()) / 255.0F;
            f[1] = ((float)getGreen()) / 255.0F;
            f[2] = ((float)getBlue()) / 255.0F;
            f[3] = ((float)getAlpha()) / 255.0F;
        } else {
            f[0] = frgbvalue[0];
            f[1] = frgbvalue[1];
            f[2] = frgbvalue[2];
            f[3] = falpha;
        }
        return f;
    }
    
    public float[] getRGBColorComponents(float[] compArray) {
        float[] f;
        if (compArray == null) {
            f = new float[3];
        } else {
            f = compArray;
        }
        if (frgbvalue == null) {
            f[0] = ((float)getRed()) / 255.0F;
            f[1] = ((float)getGreen()) / 255.0F;
            f[2] = ((float)getBlue()) / 255.0F;
        } else {
            f[0] = frgbvalue[0];
            f[1] = frgbvalue[1];
            f[2] = frgbvalue[2];
        }
        return f;
    }
    
    public float[] getComponents(float[] compArray) {
        if (fvalue == null) return getRGBComponents(compArray);
        float[] f;
        int n = fvalue.length;
        if (compArray == null) {
            f = new float[n + 1];
        } else {
            f = compArray;
        }
        for (int i = 0; i < n; i++) {
            f[i] = fvalue[i];
        }
        f[n] = falpha;
        return f;
    }
    
    public float[] getColorComponents(float[] compArray) {
        if (fvalue == null) return getRGBColorComponents(compArray);
        float[] f;
        int n = fvalue.length;
        if (compArray == null) {
            f = new float[n];
        } else {
            f = compArray;
        }
        for (int i = 0; i < n; i++) {
            f[i] = fvalue[i];
        }
        return f;
    }
    
    public float[] getComponents(ColorSpace cspace, float[] compArray) {
        if (cs == null) {
            cs = ColorSpace.getInstance(ColorSpace.CS_sRGB);
        }
        float[] f;
        if (fvalue == null) {
            f = new float[3];
            f[0] = ((float)getRed()) / 255.0F;
            f[1] = ((float)getGreen()) / 255.0F;
            f[2] = ((float)getBlue()) / 255.0F;
        } else {
            f = fvalue;
        }
        float[] tmp = cs.toCIEXYZ(f);
        float[] tmpout = cspace.fromCIEXYZ(tmp);
        if (compArray == null) {
            compArray = new float[tmpout.length + 1];
        }
        for (int i = 0; i < tmpout.length; i++) {
            compArray[i] = tmpout[i];
        }
        if (fvalue == null) {
            compArray[tmpout.length] = ((float)getAlpha()) / 255.0F;
        } else {
            compArray[tmpout.length] = falpha;
        }
        return compArray;
    }
    
    public float[] getColorComponents(ColorSpace cspace, float[] compArray) {
        if (cs == null) {
            cs = ColorSpace.getInstance(ColorSpace.CS_sRGB);
        }
        float[] f;
        if (fvalue == null) {
            f = new float[3];
            f[0] = ((float)getRed()) / 255.0F;
            f[1] = ((float)getGreen()) / 255.0F;
            f[2] = ((float)getBlue()) / 255.0F;
        } else {
            f = fvalue;
        }
        float[] tmp = cs.toCIEXYZ(f);
        float[] tmpout = cspace.fromCIEXYZ(tmp);
        if (compArray == null) {
            return tmpout;
        }
        for (int i = 0; i < tmpout.length; i++) {
            compArray[i] = tmpout[i];
        }
        return compArray;
    }
    
    public ColorSpace getColorSpace() {
        if (cs == null) {
            cs = ColorSpace.getInstance(ColorSpace.CS_sRGB);
        }
        return cs;
    }
    private transient PaintContext theContext;
    
    public synchronized PaintContext createContext(ColorModel cm, Rectangle r, Rectangle2D r2d, AffineTransform xform, RenderingHints hints) {
        PaintContext pc = theContext;
        if (pc == null) {
            pc = new ColorPaintContext(value, cm);
            theContext = pc;
        }
        return pc;
    }
    
    public int getTransparency() {
        int alpha = getAlpha();
        if (alpha == 255) {
            return Transparency.OPAQUE;
        } else if (alpha == 0) {
            return Transparency.BITMASK;
        } else {
            return Transparency.TRANSLUCENT;
        }
    }
}
