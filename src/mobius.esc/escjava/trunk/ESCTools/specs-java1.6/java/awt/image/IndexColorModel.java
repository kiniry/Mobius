package java.awt.image;

import java.awt.color.ColorSpace;
import java.math.BigInteger;

public class IndexColorModel extends ColorModel {
    private int[] rgb;
    private int map_size;
    private int transparent_index = -1;
    private boolean allgrayopaque;
    private BigInteger validBits;
    private static int[] opaqueBits = {8, 8, 8};
    private static int[] alphaBits = {8, 8, 8, 8};
    
    private static native void initIDs();
    static {
        ColorModel.loadLibraries();
        initIDs();
    }
    
    public IndexColorModel(int bits, int size, byte[] r, byte[] g, byte[] b) {
        super(bits, opaqueBits, ColorSpace.getInstance(ColorSpace.CS_sRGB), false, false, OPAQUE, ColorModel.getDefaultTransferType(bits));
        if (bits < 1 || bits > 16) {
            throw new IllegalArgumentException("Number of bits must be between 1 and 16.");
        }
        setRGBs(size, r, g, b, null);
    }
    
    public IndexColorModel(int bits, int size, byte[] r, byte[] g, byte[] b, int trans) {
        super(bits, opaqueBits, ColorSpace.getInstance(ColorSpace.CS_sRGB), false, false, OPAQUE, ColorModel.getDefaultTransferType(bits));
        if (bits < 1 || bits > 16) {
            throw new IllegalArgumentException("Number of bits must be between 1 and 16.");
        }
        setRGBs(size, r, g, b, null);
        setTransparentPixel(trans);
    }
    
    public IndexColorModel(int bits, int size, byte[] r, byte[] g, byte[] b, byte[] a) {
        super(bits, alphaBits, ColorSpace.getInstance(ColorSpace.CS_sRGB), true, false, TRANSLUCENT, ColorModel.getDefaultTransferType(bits));
        if (bits < 1 || bits > 16) {
            throw new IllegalArgumentException("Number of bits must be between 1 and 16.");
        }
        setRGBs(size, r, g, b, a);
    }
    
    public IndexColorModel(int bits, int size, byte[] cmap, int start, boolean hasalpha) {
        this(bits, size, cmap, start, hasalpha, -1);
        if (bits < 1 || bits > 16) {
            throw new IllegalArgumentException("Number of bits must be between 1 and 16.");
        }
    }
    
    public IndexColorModel(int bits, int size, byte[] cmap, int start, boolean hasalpha, int trans) {
        super(bits, opaqueBits, ColorSpace.getInstance(ColorSpace.CS_sRGB), false, false, OPAQUE, ColorModel.getDefaultTransferType(bits));
        if (bits < 1 || bits > 16) {
            throw new IllegalArgumentException("Number of bits must be between 1 and 16.");
        }
        if (size < 1) {
            throw new IllegalArgumentException("Map size (" + size + ") must be >= 1");
        }
        map_size = size;
        rgb = new int[calcRealMapSize(bits, size)];
        int j = start;
        int alpha = 255;
        boolean allgray = true;
        int transparency = OPAQUE;
        for (int i = 0; i < size; i++) {
            int r = cmap[j++] & 255;
            int g = cmap[j++] & 255;
            int b = cmap[j++] & 255;
            allgray = allgray && (r == g) && (g == b);
            if (hasalpha) {
                alpha = cmap[j++] & 255;
                if (alpha != 255) {
                    if (alpha == 0) {
                        if (transparency == OPAQUE) {
                            transparency = BITMASK;
                        }
                        if (transparent_index < 0) {
                            transparent_index = i;
                        }
                    } else {
                        transparency = TRANSLUCENT;
                    }
                    allgray = false;
                }
            }
            rgb[i] = (alpha << 24) | (r << 16) | (g << 8) | b;
        }
        this.allgrayopaque = allgray;
        setTransparency(transparency);
        setTransparentPixel(trans);
    }
    
    public IndexColorModel(int bits, int size, int[] cmap, int start, boolean hasalpha, int trans, int transferType) {
        super(bits, opaqueBits, ColorSpace.getInstance(ColorSpace.CS_sRGB), false, false, OPAQUE, transferType);
        if (bits < 1 || bits > 16) {
            throw new IllegalArgumentException("Number of bits must be between 1 and 16.");
        }
        if (size < 1) {
            throw new IllegalArgumentException("Map size (" + size + ") must be >= 1");
        }
        if ((transferType != DataBuffer.TYPE_BYTE) && (transferType != DataBuffer.TYPE_USHORT)) {
            throw new IllegalArgumentException("transferType must be eitherDataBuffer.TYPE_BYTE or DataBuffer.TYPE_USHORT");
        }
        setRGBs(size, cmap, start, hasalpha);
        setTransparentPixel(trans);
    }
    
    public IndexColorModel(int bits, int size, int[] cmap, int start, int transferType, BigInteger validBits) {
        super(bits, alphaBits, ColorSpace.getInstance(ColorSpace.CS_sRGB), true, false, TRANSLUCENT, transferType);
        if (bits < 1 || bits > 16) {
            throw new IllegalArgumentException("Number of bits must be between 1 and 16.");
        }
        if (size < 1) {
            throw new IllegalArgumentException("Map size (" + size + ") must be >= 1");
        }
        if ((transferType != DataBuffer.TYPE_BYTE) && (transferType != DataBuffer.TYPE_USHORT)) {
            throw new IllegalArgumentException("transferType must be eitherDataBuffer.TYPE_BYTE or DataBuffer.TYPE_USHORT");
        }
        if (validBits != null) {
            for (int i = 0; i < size; i++) {
                if (!validBits.testBit(i)) {
                    this.validBits = validBits;
                    break;
                }
            }
        }
        setRGBs(size, cmap, start, true);
    }
    
    private void setRGBs(int size, byte[] r, byte[] g, byte[] b, byte[] a) {
        if (size < 1) {
            throw new IllegalArgumentException("Map size (" + size + ") must be >= 1");
        }
        map_size = size;
        rgb = new int[calcRealMapSize(pixel_bits, size)];
        int alpha = 255;
        int transparency = OPAQUE;
        boolean allgray = true;
        for (int i = 0; i < size; i++) {
            int rc = r[i] & 255;
            int gc = g[i] & 255;
            int bc = b[i] & 255;
            allgray = allgray && (rc == gc) && (gc == bc);
            if (a != null) {
                alpha = a[i] & 255;
                if (alpha != 255) {
                    if (alpha == 0) {
                        if (transparency == OPAQUE) {
                            transparency = BITMASK;
                        }
                        if (transparent_index < 0) {
                            transparent_index = i;
                        }
                    } else {
                        transparency = TRANSLUCENT;
                    }
                    allgray = false;
                }
            }
            rgb[i] = (alpha << 24) | (rc << 16) | (gc << 8) | bc;
        }
        this.allgrayopaque = allgray;
        setTransparency(transparency);
    }
    
    private void setRGBs(int size, int[] cmap, int start, boolean hasalpha) {
        map_size = size;
        rgb = new int[calcRealMapSize(pixel_bits, size)];
        int j = start;
        int transparency = OPAQUE;
        boolean allgray = true;
        BigInteger validBits = this.validBits;
        for (int i = 0; i < size; i++, j++) {
            if (validBits != null && !validBits.testBit(i)) {
                continue;
            }
            int cmaprgb = cmap[j];
            int r = (cmaprgb >> 16) & 255;
            int g = (cmaprgb >> 8) & 255;
            int b = (cmaprgb) & 255;
            allgray = allgray && (r == g) && (g == b);
            if (hasalpha) {
                int alpha = cmaprgb >>> 24;
                if (alpha != 255) {
                    if (alpha == 0) {
                        if (transparency == OPAQUE) {
                            transparency = BITMASK;
                        }
                        if (transparent_index < 0) {
                            transparent_index = i;
                        }
                    } else {
                        transparency = TRANSLUCENT;
                    }
                    allgray = false;
                }
            } else {
                cmaprgb |= -16777216;
            }
            rgb[i] = cmaprgb;
        }
        this.allgrayopaque = allgray;
        setTransparency(transparency);
    }
    
    private int calcRealMapSize(int bits, int size) {
        int newSize = Math.max(1 << bits, size);
        return Math.max(newSize, 256);
    }
    
    private BigInteger getAllValid() {
        int numbytes = (map_size + 7) / 8;
        byte[] valid = new byte[numbytes];
        java.util.Arrays.fill(valid, (byte)255);
        valid[0] = (byte)(255 >>> (numbytes * 8 - map_size));
        return new BigInteger(1, valid);
    }
    
    public int getTransparency() {
        return transparency;
    }
    
    public int[] getComponentSize() {
        if (nBits == null) {
            if (supportsAlpha) {
                nBits = new int[4];
                nBits[3] = 8;
            } else {
                nBits = new int[3];
            }
            nBits[0] = nBits[1] = nBits[2] = 8;
        }
        return nBits;
    }
    
    public final int getMapSize() {
        return map_size;
    }
    
    public final int getTransparentPixel() {
        return transparent_index;
    }
    
    public final void getReds(byte[] r) {
        for (int i = 0; i < map_size; i++) {
            r[i] = (byte)(rgb[i] >> 16);
        }
    }
    
    public final void getGreens(byte[] g) {
        for (int i = 0; i < map_size; i++) {
            g[i] = (byte)(rgb[i] >> 8);
        }
    }
    
    public final void getBlues(byte[] b) {
        for (int i = 0; i < map_size; i++) {
            b[i] = (byte)rgb[i];
        }
    }
    
    public final void getAlphas(byte[] a) {
        for (int i = 0; i < map_size; i++) {
            a[i] = (byte)(rgb[i] >> 24);
        }
    }
    
    public final void getRGBs(int[] rgb) {
        System.arraycopy(this.rgb, 0, rgb, 0, map_size);
    }
    
    private void setTransparentPixel(int trans) {
        if (trans >= 0 && trans < map_size) {
            rgb[trans] &= 16777215;
            transparent_index = trans;
            allgrayopaque = false;
            if (this.transparency == OPAQUE) {
                setTransparency(BITMASK);
            }
        }
    }
    
    private void setTransparency(int transparency) {
        if (this.transparency != transparency) {
            this.transparency = transparency;
            if (transparency == OPAQUE) {
                supportsAlpha = false;
                numComponents = 3;
                nBits = opaqueBits;
            } else {
                supportsAlpha = true;
                numComponents = 4;
                nBits = alphaBits;
            }
        }
    }
    
    public final int getRed(int pixel) {
        return (rgb[pixel] >> 16) & 255;
    }
    
    public final int getGreen(int pixel) {
        return (rgb[pixel] >> 8) & 255;
    }
    
    public final int getBlue(int pixel) {
        return rgb[pixel] & 255;
    }
    
    public final int getAlpha(int pixel) {
        return (rgb[pixel] >> 24) & 255;
    }
    
    public final int getRGB(int pixel) {
        return rgb[pixel];
    }
    private static final int CACHESIZE = 40;
    private int[] lookupcache = new int[CACHESIZE];
    
    public synchronized Object getDataElements(int rgb, Object pixel) {
        int red = (rgb >> 16) & 255;
        int green = (rgb >> 8) & 255;
        int blue = rgb & 255;
        int alpha = (rgb >>> 24);
        int pix = 0;
        for (int i = CACHESIZE - 2; i >= 0; i -= 2) {
            if ((pix = lookupcache[i]) == 0) {
                break;
            }
            if (rgb == lookupcache[i + 1]) {
                return installpixel(pixel, ~pix);
            }
        }
        if (allgrayopaque) {
            int minDist = 256;
            int d;
            int gray = (int)(red * 77 + green * 150 + blue * 29 + 128) / 256;
            for (int i = 0; i < map_size; i++) {
                if (this.rgb[i] == 0) {
                    continue;
                }
                d = (this.rgb[i] & 255) - gray;
                if (d < 0) d = -d;
                if (d < minDist) {
                    pix = i;
                    if (d == 0) {
                        break;
                    }
                    minDist = d;
                }
            }
        } else if (alpha == 0) {
            if (transparent_index >= 0) {
                pix = transparent_index;
            } else {
                int smallestAlpha = 256;
                for (int i = 0; i < map_size; i++) {
                    int a = this.rgb[i] >>> 24;
                    if (smallestAlpha > alpha && (validBits == null || validBits.testBit(i))) {
                        smallestAlpha = alpha;
                        pix = i;
                    }
                }
            }
        } else {
            int smallestError = 255 * 255 * 255;
            int smallestAlphaError = 255;
            ;
            for (int i = 0; i < map_size; i++) {
                int lutrgb = this.rgb[i];
                if (lutrgb == rgb) {
                    pix = i;
                    break;
                }
                int tmp = (lutrgb >>> 24) - alpha;
                if (tmp < 0) {
                    tmp = -tmp;
                }
                if (tmp <= smallestAlphaError) {
                    smallestAlphaError = tmp;
                    tmp = ((lutrgb >> 16) & 255) - red;
                    int currentError = tmp * tmp;
                    if (currentError < smallestError) {
                        tmp = ((lutrgb >> 8) & 255) - green;
                        currentError += tmp * tmp;
                        if (currentError < smallestError) {
                            tmp = (lutrgb & 255) - blue;
                            currentError += tmp * tmp;
                            if (currentError < smallestError && (validBits == null || validBits.testBit(i))) {
                                pix = i;
                                smallestError = currentError;
                            }
                        }
                    }
                }
            }
        }
        System.arraycopy(lookupcache, 2, lookupcache, 0, CACHESIZE - 2);
        lookupcache[CACHESIZE - 1] = rgb;
        lookupcache[CACHESIZE - 2] = ~pix;
        return installpixel(pixel, pix);
    }
    
    private Object installpixel(Object pixel, int pix) {
        switch (transferType) {
        case DataBuffer.TYPE_INT: 
            int[] intObj;
            if (pixel == null) {
                pixel = intObj = new int[1];
            } else {
                intObj = (int[])(int[])pixel;
            }
            intObj[0] = pix;
            break;
        
        case DataBuffer.TYPE_BYTE: 
            byte[] byteObj;
            if (pixel == null) {
                pixel = byteObj = new byte[1];
            } else {
                byteObj = (byte[])(byte[])pixel;
            }
            byteObj[0] = (byte)pix;
            break;
        
        case DataBuffer.TYPE_USHORT: 
            short[] shortObj;
            if (pixel == null) {
                pixel = shortObj = new short[1];
            } else {
                shortObj = (short[])(short[])pixel;
            }
            shortObj[0] = (short)pix;
            break;
        
        default: 
            throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
        
        }
        return pixel;
    }
    
    public int[] getComponents(int pixel, int[] components, int offset) {
        if (components == null) {
            components = new int[offset + numComponents];
        }
        components[offset + 0] = getRed(pixel);
        components[offset + 1] = getGreen(pixel);
        components[offset + 2] = getBlue(pixel);
        if (supportsAlpha && (components.length - offset) > 3) {
            components[offset + 3] = getAlpha(pixel);
        }
        return components;
    }
    
    public int[] getComponents(Object pixel, int[] components, int offset) {
        int intpixel;
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            byte[] bdata = (byte[])(byte[])pixel;
            intpixel = bdata[0] & 255;
            break;
        
        case DataBuffer.TYPE_USHORT: 
            short[] sdata = (short[])(short[])pixel;
            intpixel = sdata[0] & 65535;
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] idata = (int[])(int[])pixel;
            intpixel = idata[0];
            break;
        
        default: 
            throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
        
        }
        return getComponents(intpixel, components, offset);
    }
    
    public int getDataElement(int[] components, int offset) {
        int rgb = (components[offset + 0] << 16) | (components[offset + 1] << 8) | (components[offset + 2]);
        if (supportsAlpha) {
            rgb |= (components[offset + 3] << 24);
        } else {
            rgb |= -16777216;
        }
        Object inData = getDataElements(rgb, null);
        int pixel;
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            byte[] bdata = (byte[])(byte[])inData;
            pixel = bdata[0] & 255;
            break;
        
        case DataBuffer.TYPE_USHORT: 
            short[] sdata = (short[])(short[])inData;
            pixel = sdata[0];
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] idata = (int[])(int[])inData;
            pixel = idata[0];
            break;
        
        default: 
            throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
        
        }
        return pixel;
    }
    
    public Object getDataElements(int[] components, int offset, Object pixel) {
        int rgb = (components[offset + 0] << 16) | (components[offset + 1] << 8) | (components[offset + 2]);
        if (supportsAlpha) {
            rgb |= (components[offset + 3] << 24);
        } else {
            rgb &= -16777216;
        }
        return getDataElements(rgb, pixel);
    }
    
    public WritableRaster createCompatibleWritableRaster(int w, int h) {
        WritableRaster raster;
        if (pixel_bits == 1 || pixel_bits == 2 || pixel_bits == 4) {
            raster = Raster.createPackedRaster(DataBuffer.TYPE_BYTE, w, h, 1, pixel_bits, null);
        } else if (pixel_bits <= 8) {
            raster = Raster.createInterleavedRaster(DataBuffer.TYPE_BYTE, w, h, 1, null);
        } else if (pixel_bits <= 16) {
            raster = Raster.createInterleavedRaster(DataBuffer.TYPE_USHORT, w, h, 1, null);
        } else {
            throw new UnsupportedOperationException("This method is not supported  for pixel bits > 16.");
        }
        return raster;
    }
    
    public boolean isCompatibleRaster(Raster raster) {
        int size = raster.getSampleModel().getSampleSize(0);
        return ((raster.getTransferType() == transferType) && (raster.getNumBands() == 1) && ((1 << size) >= map_size));
    }
    
    public SampleModel createCompatibleSampleModel(int w, int h) {
        int[] off = new int[1];
        off[0] = 0;
        if (pixel_bits == 1 || pixel_bits == 2 || pixel_bits == 4) {
            return new MultiPixelPackedSampleModel(transferType, w, h, pixel_bits);
        } else {
            return new ComponentSampleModel(transferType, w, h, 1, w, off);
        }
    }
    
    public boolean isCompatibleSampleModel(SampleModel sm) {
        if (!(sm instanceof ComponentSampleModel) && !(sm instanceof MultiPixelPackedSampleModel)) {
            return false;
        }
        if (sm.getTransferType() != transferType) {
            return false;
        }
        if (sm.getNumBands() != 1) {
            return false;
        }
        return true;
    }
    
    public BufferedImage convertToIntDiscrete(Raster raster, boolean forceARGB) {
        ColorModel cm;
        if (!isCompatibleRaster(raster)) {
            throw new IllegalArgumentException("This raster is not compatiblewith this IndexColorModel.");
        }
        if (forceARGB || transparency == TRANSLUCENT) {
            cm = ColorModel.getRGBdefault();
        } else if (transparency == BITMASK) {
            cm = new DirectColorModel(25, 16711680, 65280, 255, 16777216);
        } else {
            cm = new DirectColorModel(24, 16711680, 65280, 255);
        }
        int w = raster.getWidth();
        int h = raster.getHeight();
        WritableRaster discreteRaster = cm.createCompatibleWritableRaster(w, h);
        Object obj = null;
        int[] data = null;
        int rX = raster.getMinX();
        int rY = raster.getMinY();
        for (int y = 0; y < h; y++, rY++) {
            obj = raster.getDataElements(rX, rY, w, 1, obj);
            if (obj instanceof int[]) {
                data = (int[])(int[])obj;
            } else {
                data = DataBuffer.toIntArray(obj);
            }
            for (int x = 0; x < w; x++) {
                data[x] = rgb[data[x]];
            }
            discreteRaster.setDataElements(0, y, w, 1, data);
        }
        return new BufferedImage(cm, discreteRaster, false, null);
    }
    
    public boolean isValid(int pixel) {
        return ((pixel >= 0 && pixel < map_size) && (validBits == null || validBits.testBit(pixel)));
    }
    
    public boolean isValid() {
        return (validBits == null);
    }
    
    public BigInteger getValidPixels() {
        if (validBits == null) {
            return getAllValid();
        } else {
            return validBits;
        }
    }
    
    public void finalize() {
        sun.awt.image.BufImgSurfaceData.freeNativeICMData(this);
    }
    
    public String toString() {
        return new String("IndexColorModel: #pixelBits = " + pixel_bits + " numComponents = " + numComponents + " color space = " + colorSpace + " transparency = " + transparency + " transIndex   = " + transparent_index + " has alpha = " + supportsAlpha + " isAlphaPre = " + isAlphaPremultiplied);
    }
}
