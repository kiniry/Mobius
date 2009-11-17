package java.awt.image;

import java.awt.Transparency;
import java.awt.color.ColorSpace;
import java.awt.color.ICC_ColorSpace;
import sun.awt.color.ICC_Transform;
import sun.awt.color.CMM;
import java.util.Collections;
import java.util.Map;
import java.util.WeakHashMap;

public abstract class ColorModel implements Transparency {
    private long pData;
    protected int pixel_bits;
    int[] nBits;
    int transparency = Transparency.TRANSLUCENT;
    boolean supportsAlpha = true;
    boolean isAlphaPremultiplied = false;
    int numComponents = -1;
    int numColorComponents = -1;
    ColorSpace colorSpace = ColorSpace.getInstance(ColorSpace.CS_sRGB);
    int colorSpaceType = ColorSpace.TYPE_RGB;
    int maxBits;
    boolean is_sRGB = true;
    protected int transferType;
    private static boolean loaded = false;
    
    static void loadLibraries() {
        if (!loaded) {
            java.security.AccessController.doPrivileged(new sun.security.action.LoadLibraryAction("awt"));
            loaded = true;
        }
    }
    
    private static native void initIDs();
    static {
        loadLibraries();
        initIDs();
    }
    private static ColorModel RGBdefault;
    
    public static ColorModel getRGBdefault() {
        if (RGBdefault == null) {
            RGBdefault = new DirectColorModel(32, 16711680, 65280, 255, -16777216);
        }
        return RGBdefault;
    }
    
    public ColorModel(int bits) {
        
        pixel_bits = bits;
        if (bits < 1) {
            throw new IllegalArgumentException("Number of bits must be > 0");
        }
        numComponents = 4;
        numColorComponents = 3;
        maxBits = bits;
        transferType = ColorModel.getDefaultTransferType(bits);
    }
    
    protected ColorModel(int pixel_bits, int[] bits, ColorSpace cspace, boolean hasAlpha, boolean isAlphaPremultiplied, int transparency, int transferType) {
        
        colorSpace = cspace;
        colorSpaceType = cspace.getType();
        numColorComponents = cspace.getNumComponents();
        numComponents = numColorComponents + (hasAlpha ? 1 : 0);
        supportsAlpha = hasAlpha;
        if (bits.length < numComponents) {
            throw new IllegalArgumentException("Number of color/alpha " + "components should be " + numComponents + " but length of bits array is " + bits.length);
        }
        if (transparency < Transparency.OPAQUE || transparency > Transparency.TRANSLUCENT) {
            throw new IllegalArgumentException("Unknown transparency: " + transparency);
        }
        if (supportsAlpha == false) {
            this.isAlphaPremultiplied = false;
            this.transparency = Transparency.OPAQUE;
        } else {
            this.isAlphaPremultiplied = isAlphaPremultiplied;
            this.transparency = transparency;
        }
        nBits = (int[])(int[])bits.clone();
        this.pixel_bits = pixel_bits;
        if (pixel_bits <= 0) {
            throw new IllegalArgumentException("Number of pixel bits must be > 0");
        }
        maxBits = 0;
        for (int i = 0; i < bits.length; i++) {
            if (bits[i] < 0) {
                throw new IllegalArgumentException("Number of bits must be >= 0");
            }
            if (maxBits < bits[i]) {
                maxBits = bits[i];
            }
        }
        if (maxBits == 0) {
            throw new IllegalArgumentException("There must be at least one component with > 0 pixel bits.");
        }
        if (cspace != ColorSpace.getInstance(ColorSpace.CS_sRGB)) {
            is_sRGB = false;
        }
        this.transferType = transferType;
    }
    
    public final boolean hasAlpha() {
        return supportsAlpha;
    }
    
    public final boolean isAlphaPremultiplied() {
        return isAlphaPremultiplied;
    }
    
    public final int getTransferType() {
        return transferType;
    }
    
    public int getPixelSize() {
        return pixel_bits;
    }
    
    public int getComponentSize(int componentIdx) {
        if (nBits == null) {
            throw new NullPointerException("Number of bits array is null.");
        }
        return nBits[componentIdx];
    }
    
    public int[] getComponentSize() {
        if (nBits != null) {
            return (int[])(int[])nBits.clone();
        }
        return null;
    }
    
    public int getTransparency() {
        return transparency;
    }
    
    public int getNumComponents() {
        return numComponents;
    }
    
    public int getNumColorComponents() {
        return numColorComponents;
    }
    
    public abstract int getRed(int pixel);
    
    public abstract int getGreen(int pixel);
    
    public abstract int getBlue(int pixel);
    
    public abstract int getAlpha(int pixel);
    
    public int getRGB(int pixel) {
        return (getAlpha(pixel) << 24) | (getRed(pixel) << 16) | (getGreen(pixel) << 8) | (getBlue(pixel) << 0);
    }
    
    public int getRed(Object inData) {
        int pixel = 0;
        int length = 0;
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            byte[] bdata = (byte[])(byte[])inData;
            pixel = bdata[0] & 255;
            length = bdata.length;
            break;
        
        case DataBuffer.TYPE_USHORT: 
            short[] sdata = (short[])(short[])inData;
            pixel = sdata[0] & 65535;
            length = sdata.length;
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] idata = (int[])(int[])inData;
            pixel = idata[0];
            length = idata.length;
            break;
        
        default: 
            throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
        
        }
        if (length == 1) {
            return getRed(pixel);
        } else {
            throw new UnsupportedOperationException("This method is not supported by this color model");
        }
    }
    
    public int getGreen(Object inData) {
        int pixel = 0;
        int length = 0;
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            byte[] bdata = (byte[])(byte[])inData;
            pixel = bdata[0] & 255;
            length = bdata.length;
            break;
        
        case DataBuffer.TYPE_USHORT: 
            short[] sdata = (short[])(short[])inData;
            pixel = sdata[0] & 65535;
            length = sdata.length;
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] idata = (int[])(int[])inData;
            pixel = idata[0];
            length = idata.length;
            break;
        
        default: 
            throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
        
        }
        if (length == 1) {
            return getGreen(pixel);
        } else {
            throw new UnsupportedOperationException("This method is not supported by this color model");
        }
    }
    
    public int getBlue(Object inData) {
        int pixel = 0;
        int length = 0;
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            byte[] bdata = (byte[])(byte[])inData;
            pixel = bdata[0] & 255;
            length = bdata.length;
            break;
        
        case DataBuffer.TYPE_USHORT: 
            short[] sdata = (short[])(short[])inData;
            pixel = sdata[0] & 65535;
            length = sdata.length;
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] idata = (int[])(int[])inData;
            pixel = idata[0];
            length = idata.length;
            break;
        
        default: 
            throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
        
        }
        if (length == 1) {
            return getBlue(pixel);
        } else {
            throw new UnsupportedOperationException("This method is not supported by this color model");
        }
    }
    
    public int getAlpha(Object inData) {
        int pixel = 0;
        int length = 0;
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            byte[] bdata = (byte[])(byte[])inData;
            pixel = bdata[0] & 255;
            length = bdata.length;
            break;
        
        case DataBuffer.TYPE_USHORT: 
            short[] sdata = (short[])(short[])inData;
            pixel = sdata[0] & 65535;
            length = sdata.length;
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] idata = (int[])(int[])inData;
            pixel = idata[0];
            length = idata.length;
            break;
        
        default: 
            throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
        
        }
        if (length == 1) {
            return getAlpha(pixel);
        } else {
            throw new UnsupportedOperationException("This method is not supported by this color model");
        }
    }
    
    public int getRGB(Object inData) {
        return (getAlpha(inData) << 24) | (getRed(inData) << 16) | (getGreen(inData) << 8) | (getBlue(inData) << 0);
    }
    
    public Object getDataElements(int rgb, Object pixel) {
        throw new UnsupportedOperationException("This method is not supported by this color model.");
    }
    
    public int[] getComponents(int pixel, int[] components, int offset) {
        throw new UnsupportedOperationException("This method is not supported by this color model.");
    }
    
    public int[] getComponents(Object pixel, int[] components, int offset) {
        throw new UnsupportedOperationException("This method is not supported by this color model.");
    }
    
    public int[] getUnnormalizedComponents(float[] normComponents, int normOffset, int[] components, int offset) {
        if (colorSpace == null) {
            throw new UnsupportedOperationException("This method is not supported by this color model.");
        }
        if (nBits == null) {
            throw new UnsupportedOperationException("This method is not supported.  Unable to determine #bits per component.");
        }
        if ((normComponents.length - normOffset) < numComponents) {
            throw new IllegalArgumentException("Incorrect number of components.  Expecting " + numComponents);
        }
        if (components == null) {
            components = new int[offset + numComponents];
        }
        if (supportsAlpha && isAlphaPremultiplied) {
            float normAlpha = normComponents[normOffset + numColorComponents];
            for (int i = 0; i < numColorComponents; i++) {
                components[offset + i] = (int)(normComponents[normOffset + i] * ((1 << nBits[i]) - 1) * normAlpha + 0.5F);
            }
            components[offset + numColorComponents] = (int)(normAlpha * ((1 << nBits[numColorComponents]) - 1) + 0.5F);
        } else {
            for (int i = 0; i < numComponents; i++) {
                components[offset + i] = (int)(normComponents[normOffset + i] * ((1 << nBits[i]) - 1) + 0.5F);
            }
        }
        return components;
    }
    
    public float[] getNormalizedComponents(int[] components, int offset, float[] normComponents, int normOffset) {
        if (colorSpace == null) {
            throw new UnsupportedOperationException("This method is not supported by this color model.");
        }
        if (nBits == null) {
            throw new UnsupportedOperationException("This method is not supported.  Unable to determine #bits per component.");
        }
        if ((components.length - offset) < numComponents) {
            throw new IllegalArgumentException("Incorrect number of components.  Expecting " + numComponents);
        }
        if (normComponents == null) {
            normComponents = new float[numComponents + normOffset];
        }
        if (supportsAlpha && isAlphaPremultiplied) {
            float normAlpha = (float)components[offset + numColorComponents];
            normAlpha /= (float)((1 << nBits[numColorComponents]) - 1);
            if (normAlpha != 0.0F) {
                for (int i = 0; i < numColorComponents; i++) {
                    normComponents[normOffset + i] = ((float)components[offset + i]) / (normAlpha * ((float)((1 << nBits[i]) - 1)));
                }
            } else {
                for (int i = 0; i < numColorComponents; i++) {
                    normComponents[normOffset + i] = 0.0F;
                }
            }
            normComponents[normOffset + numColorComponents] = normAlpha;
        } else {
            for (int i = 0; i < numComponents; i++) {
                normComponents[normOffset + i] = ((float)components[offset + i]) / ((float)((1 << nBits[i]) - 1));
            }
        }
        return normComponents;
    }
    
    public int getDataElement(int[] components, int offset) {
        throw new UnsupportedOperationException("This method is not supported by this color model.");
    }
    
    public Object getDataElements(int[] components, int offset, Object obj) {
        throw new UnsupportedOperationException("This method has not been implemented for this color model.");
    }
    
    public int getDataElement(float[] normComponents, int normOffset) {
        int[] components = getUnnormalizedComponents(normComponents, normOffset, null, 0);
        return getDataElement(components, 0);
    }
    
    public Object getDataElements(float[] normComponents, int normOffset, Object obj) {
        int[] components = getUnnormalizedComponents(normComponents, normOffset, null, 0);
        return getDataElements(components, 0, obj);
    }
    
    public float[] getNormalizedComponents(Object pixel, float[] normComponents, int normOffset) {
        int[] components = getComponents(pixel, null, 0);
        return getNormalizedComponents(components, 0, normComponents, normOffset);
    }
    
    public boolean equals(Object obj) {
        if (!(obj instanceof ColorModel)) {
            return false;
        }
        ColorModel cm = (ColorModel)(ColorModel)obj;
        if (this == cm) {
            return true;
        }
        if (supportsAlpha != cm.hasAlpha() || isAlphaPremultiplied != cm.isAlphaPremultiplied() || pixel_bits != cm.getPixelSize() || transparency != cm.getTransparency() || numComponents != cm.getNumComponents()) {
            return false;
        }
        int[] nb = cm.getComponentSize();
        if ((nBits != null) && (nb != null)) {
            for (int i = 0; i < numComponents; i++) {
                if (nBits[i] != nb[i]) {
                    return false;
                }
            }
        } else {
            return ((nBits == null) && (nb == null));
        }
        return true;
    }
    
    public int hashCode() {
        int result = 0;
        result = (supportsAlpha ? 2 : 3) + (isAlphaPremultiplied ? 4 : 5) + pixel_bits * 6 + transparency * 7 + numComponents * 8;
        if (nBits != null) {
            for (int i = 0; i < numComponents; i++) {
                result = result + nBits[i] * (i + 9);
            }
        }
        return result;
    }
    
    public final ColorSpace getColorSpace() {
        return colorSpace;
    }
    
    public ColorModel coerceData(WritableRaster raster, boolean isAlphaPremultiplied) {
        throw new UnsupportedOperationException("This method is not supported by this color model");
    }
    
    public boolean isCompatibleRaster(Raster raster) {
        throw new UnsupportedOperationException("This method has not been implemented for this ColorModel.");
    }
    
    public WritableRaster createCompatibleWritableRaster(int w, int h) {
        throw new UnsupportedOperationException("This method is not supported by this color model");
    }
    
    public SampleModel createCompatibleSampleModel(int w, int h) {
        throw new UnsupportedOperationException("This method is not supported by this color model");
    }
    
    public boolean isCompatibleSampleModel(SampleModel sm) {
        throw new UnsupportedOperationException("This method is not supported by this color model");
    }
    
    public void finalize() {
    }
    
    public WritableRaster getAlphaRaster(WritableRaster raster) {
        return null;
    }
    
    public String toString() {
        return new String("ColorModel: #pixelBits = " + pixel_bits + " numComponents = " + numComponents + " color space = " + colorSpace + " transparency = " + transparency + " has alpha = " + supportsAlpha + " isAlphaPre = " + isAlphaPremultiplied);
    }
    
    static int getDefaultTransferType(int pixel_bits) {
        if (pixel_bits <= 8) {
            return DataBuffer.TYPE_BYTE;
        } else if (pixel_bits <= 16) {
            return DataBuffer.TYPE_USHORT;
        } else if (pixel_bits <= 32) {
            return DataBuffer.TYPE_INT;
        } else {
            return DataBuffer.TYPE_UNDEFINED;
        }
    }
    static byte[] l8Tos8 = null;
    static byte[] s8Tol8 = null;
    static byte[] l16Tos8 = null;
    static short[] s8Tol16 = null;
    static Map g8Tos8Map = null;
    static Map lg16Toog8Map = null;
    static Map g16Tos8Map = null;
    static Map lg16Toog16Map = null;
    
    static boolean isLinearRGBspace(ColorSpace cs) {
        return (cs == CMM.LINEAR_RGBspace);
    }
    
    static boolean isLinearGRAYspace(ColorSpace cs) {
        return (cs == CMM.GRAYspace);
    }
    
    static byte[] getLinearRGB8TosRGB8LUT() {
        if (l8Tos8 == null) {
            l8Tos8 = new byte[256];
            float input;
            float output;
            for (int i = 0; i <= 255; i++) {
                input = ((float)i) / 255.0F;
                if (input <= 0.0031308F) {
                    output = input * 12.92F;
                } else {
                    output = 1.055F * ((float)Math.pow(input, (1.0 / 2.4))) - 0.055F;
                }
                l8Tos8[i] = (byte)Math.round(output * 255.0F);
            }
        }
        return l8Tos8;
    }
    
    static byte[] getsRGB8ToLinearRGB8LUT() {
        if (s8Tol8 == null) {
            s8Tol8 = new byte[256];
            float input;
            float output;
            for (int i = 0; i <= 255; i++) {
                input = ((float)i) / 255.0F;
                if (input <= 0.04045F) {
                    output = input / 12.92F;
                } else {
                    output = (float)Math.pow((input + 0.055F) / 1.055F, 2.4);
                }
                s8Tol8[i] = (byte)Math.round(output * 255.0F);
            }
        }
        return s8Tol8;
    }
    
    static byte[] getLinearRGB16TosRGB8LUT() {
        if (l16Tos8 == null) {
            l16Tos8 = new byte[65536];
            float input;
            float output;
            for (int i = 0; i <= 65535; i++) {
                input = ((float)i) / 65535.0F;
                if (input <= 0.0031308F) {
                    output = input * 12.92F;
                } else {
                    output = 1.055F * ((float)Math.pow(input, (1.0 / 2.4))) - 0.055F;
                }
                l16Tos8[i] = (byte)Math.round(output * 255.0F);
            }
        }
        return l16Tos8;
    }
    
    static short[] getsRGB8ToLinearRGB16LUT() {
        if (s8Tol16 == null) {
            s8Tol16 = new short[256];
            float input;
            float output;
            for (int i = 0; i <= 255; i++) {
                input = ((float)i) / 255.0F;
                if (input <= 0.04045F) {
                    output = input / 12.92F;
                } else {
                    output = (float)Math.pow((input + 0.055F) / 1.055F, 2.4);
                }
                s8Tol16[i] = (short)Math.round(output * 65535.0F);
            }
        }
        return s8Tol16;
    }
    
    static byte[] getGray8TosRGB8LUT(ICC_ColorSpace grayCS) {
        if (isLinearGRAYspace(grayCS)) {
            return getLinearRGB8TosRGB8LUT();
        }
        if (g8Tos8Map != null) {
            byte[] g8Tos8LUT = (byte[])(byte[])g8Tos8Map.get(grayCS);
            if (g8Tos8LUT != null) {
                return g8Tos8LUT;
            }
        }
        byte[] g8Tos8LUT = new byte[256];
        for (int i = 0; i <= 255; i++) {
            g8Tos8LUT[i] = (byte)i;
        }
        ICC_Transform[] transformList = new ICC_Transform[2];
        ICC_ColorSpace srgbCS = (ICC_ColorSpace)(ICC_ColorSpace)ColorSpace.getInstance(ColorSpace.CS_sRGB);
        transformList[0] = new ICC_Transform(grayCS.getProfile(), ICC_Transform.Any, ICC_Transform.In);
        transformList[1] = new ICC_Transform(srgbCS.getProfile(), ICC_Transform.Any, ICC_Transform.Out);
        ICC_Transform t = new ICC_Transform(transformList);
        byte[] tmp = t.colorConvert(g8Tos8LUT, null);
        for (int i = 0, j = 2; i <= 255; i++, j += 3) {
            g8Tos8LUT[i] = tmp[j];
        }
        if (g8Tos8Map == null) {
            g8Tos8Map = Collections.synchronizedMap(new WeakHashMap(2));
        }
        g8Tos8Map.put(grayCS, g8Tos8LUT);
        return g8Tos8LUT;
    }
    
    static byte[] getLinearGray16ToOtherGray8LUT(ICC_ColorSpace grayCS) {
        if (lg16Toog8Map != null) {
            byte[] lg16Toog8LUT = (byte[])(byte[])lg16Toog8Map.get(grayCS);
            if (lg16Toog8LUT != null) {
                return lg16Toog8LUT;
            }
        }
        short[] tmp = new short[65536];
        for (int i = 0; i <= 65535; i++) {
            tmp[i] = (short)i;
        }
        ICC_Transform[] transformList = new ICC_Transform[2];
        ICC_ColorSpace lgCS = (ICC_ColorSpace)(ICC_ColorSpace)ColorSpace.getInstance(ColorSpace.CS_GRAY);
        transformList[0] = new ICC_Transform(lgCS.getProfile(), ICC_Transform.Any, ICC_Transform.In);
        transformList[1] = new ICC_Transform(grayCS.getProfile(), ICC_Transform.Any, ICC_Transform.Out);
        ICC_Transform t = new ICC_Transform(transformList);
        tmp = t.colorConvert(tmp, null);
        byte[] lg16Toog8LUT = new byte[65536];
        for (int i = 0; i <= 65535; i++) {
            lg16Toog8LUT[i] = (byte)(((float)(tmp[i] & 65535)) * (1.0F / 257.0F) + 0.5F);
        }
        if (lg16Toog8Map == null) {
            lg16Toog8Map = Collections.synchronizedMap(new WeakHashMap(2));
        }
        lg16Toog8Map.put(grayCS, lg16Toog8LUT);
        return lg16Toog8LUT;
    }
    
    static byte[] getGray16TosRGB8LUT(ICC_ColorSpace grayCS) {
        if (isLinearGRAYspace(grayCS)) {
            return getLinearRGB16TosRGB8LUT();
        }
        if (g16Tos8Map != null) {
            byte[] g16Tos8LUT = (byte[])(byte[])g16Tos8Map.get(grayCS);
            if (g16Tos8LUT != null) {
                return g16Tos8LUT;
            }
        }
        short[] tmp = new short[65536];
        for (int i = 0; i <= 65535; i++) {
            tmp[i] = (short)i;
        }
        ICC_Transform[] transformList = new ICC_Transform[2];
        ICC_ColorSpace srgbCS = (ICC_ColorSpace)(ICC_ColorSpace)ColorSpace.getInstance(ColorSpace.CS_sRGB);
        transformList[0] = new ICC_Transform(grayCS.getProfile(), ICC_Transform.Any, ICC_Transform.In);
        transformList[1] = new ICC_Transform(srgbCS.getProfile(), ICC_Transform.Any, ICC_Transform.Out);
        ICC_Transform t = new ICC_Transform(transformList);
        tmp = t.colorConvert(tmp, null);
        byte[] g16Tos8LUT = new byte[65536];
        for (int i = 0, j = 2; i <= 65535; i++, j += 3) {
            g16Tos8LUT[i] = (byte)(((float)(tmp[j] & 65535)) * (1.0F / 257.0F) + 0.5F);
        }
        if (g16Tos8Map == null) {
            g16Tos8Map = Collections.synchronizedMap(new WeakHashMap(2));
        }
        g16Tos8Map.put(grayCS, g16Tos8LUT);
        return g16Tos8LUT;
    }
    
    static short[] getLinearGray16ToOtherGray16LUT(ICC_ColorSpace grayCS) {
        if (lg16Toog16Map != null) {
            short[] lg16Toog16LUT = (short[])(short[])lg16Toog16Map.get(grayCS);
            if (lg16Toog16LUT != null) {
                return lg16Toog16LUT;
            }
        }
        short[] tmp = new short[65536];
        for (int i = 0; i <= 65535; i++) {
            tmp[i] = (short)i;
        }
        ICC_Transform[] transformList = new ICC_Transform[2];
        ICC_ColorSpace lgCS = (ICC_ColorSpace)(ICC_ColorSpace)ColorSpace.getInstance(ColorSpace.CS_GRAY);
        transformList[0] = new ICC_Transform(lgCS.getProfile(), ICC_Transform.Any, ICC_Transform.In);
        transformList[1] = new ICC_Transform(grayCS.getProfile(), ICC_Transform.Any, ICC_Transform.Out);
        ICC_Transform t = new ICC_Transform(transformList);
        short[] lg16Toog16LUT = t.colorConvert(tmp, null);
        if (lg16Toog16Map == null) {
            lg16Toog16Map = Collections.synchronizedMap(new WeakHashMap(2));
        }
        lg16Toog16Map.put(grayCS, lg16Toog16LUT);
        return lg16Toog16LUT;
    }
}
