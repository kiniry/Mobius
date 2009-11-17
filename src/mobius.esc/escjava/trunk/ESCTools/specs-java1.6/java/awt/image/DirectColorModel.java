package java.awt.image;

import java.awt.color.ColorSpace;
import java.awt.Transparency;

public class DirectColorModel extends PackedColorModel {
    private int red_mask;
    private int green_mask;
    private int blue_mask;
    private int alpha_mask;
    private int red_offset;
    private int green_offset;
    private int blue_offset;
    private int alpha_offset;
    private int red_scale;
    private int green_scale;
    private int blue_scale;
    private int alpha_scale;
    private boolean is_LinearRGB;
    private int lRGBprecision;
    private byte[] tosRGB8LUT;
    private byte[] fromsRGB8LUT8;
    private short[] fromsRGB8LUT16;
    
    public DirectColorModel(int bits, int rmask, int gmask, int bmask) {
        this(bits, rmask, gmask, bmask, 0);
    }
    
    public DirectColorModel(int bits, int rmask, int gmask, int bmask, int amask) {
        super(ColorSpace.getInstance(ColorSpace.CS_sRGB), bits, rmask, gmask, bmask, amask, false, amask == 0 ? Transparency.OPAQUE : Transparency.TRANSLUCENT, ColorModel.getDefaultTransferType(bits));
        setFields();
    }
    
    public DirectColorModel(ColorSpace space, int bits, int rmask, int gmask, int bmask, int amask, boolean isAlphaPremultiplied, int transferType) {
        super(space, bits, rmask, gmask, bmask, amask, isAlphaPremultiplied, amask == 0 ? Transparency.OPAQUE : Transparency.TRANSLUCENT, transferType);
        if (ColorModel.isLinearRGBspace(colorSpace)) {
            is_LinearRGB = true;
            if (maxBits <= 8) {
                lRGBprecision = 8;
                tosRGB8LUT = ColorModel.getLinearRGB8TosRGB8LUT();
                fromsRGB8LUT8 = ColorModel.getsRGB8ToLinearRGB8LUT();
            } else {
                lRGBprecision = 16;
                tosRGB8LUT = ColorModel.getLinearRGB16TosRGB8LUT();
                fromsRGB8LUT16 = ColorModel.getsRGB8ToLinearRGB16LUT();
            }
        } else if (!is_sRGB) {
            for (int i = 0; i < 3; i++) {
                if ((space.getMinValue(i) != 0.0F) || (space.getMaxValue(i) != 1.0F)) {
                    throw new IllegalArgumentException("Illegal min/max RGB component value");
                }
            }
        }
        setFields();
    }
    
    public final int getRedMask() {
        return maskArray[0];
    }
    
    public final int getGreenMask() {
        return maskArray[1];
    }
    
    public final int getBlueMask() {
        return maskArray[2];
    }
    
    public final int getAlphaMask() {
        if (supportsAlpha) {
            return maskArray[3];
        } else {
            return 0;
        }
    }
    
    private float[] getDefaultRGBComponents(int pixel) {
        int[] components = getComponents(pixel, null, 0);
        float[] norm = getNormalizedComponents(components, 0, null, 0);
        return colorSpace.toRGB(norm);
    }
    
    private int getsRGBComponentFromsRGB(int pixel, int idx) {
        int c = ((pixel & maskArray[idx]) >>> maskOffsets[idx]);
        if (isAlphaPremultiplied) {
            int a = ((pixel & maskArray[3]) >>> maskOffsets[3]);
            c = (a == 0) ? 0 : (int)(((c * scaleFactors[idx]) * 255.0F / (a * scaleFactors[3])) + 0.5F);
        } else if (scaleFactors[idx] != 1.0F) {
            c = (int)((c * scaleFactors[idx]) + 0.5F);
        }
        return c;
    }
    
    private int getsRGBComponentFromLinearRGB(int pixel, int idx) {
        int c = ((pixel & maskArray[idx]) >>> maskOffsets[idx]);
        if (isAlphaPremultiplied) {
            float factor = (float)((1 << lRGBprecision) - 1);
            int a = ((pixel & maskArray[3]) >>> maskOffsets[3]);
            c = (a == 0) ? 0 : (int)(((c * scaleFactors[idx]) * factor / (a * scaleFactors[3])) + 0.5F);
        } else if (nBits[idx] != lRGBprecision) {
            if (lRGBprecision == 16) {
                c = (int)((c * scaleFactors[idx] * 257.0F) + 0.5F);
            } else {
                c = (int)((c * scaleFactors[idx]) + 0.5F);
            }
        }
        return tosRGB8LUT[c] & 255;
    }
    
    public final int getRed(int pixel) {
        if (is_sRGB) {
            return getsRGBComponentFromsRGB(pixel, 0);
        } else if (is_LinearRGB) {
            return getsRGBComponentFromLinearRGB(pixel, 0);
        }
        float[] rgb = getDefaultRGBComponents(pixel);
        return (int)(rgb[0] * 255.0F + 0.5F);
    }
    
    public final int getGreen(int pixel) {
        if (is_sRGB) {
            return getsRGBComponentFromsRGB(pixel, 1);
        } else if (is_LinearRGB) {
            return getsRGBComponentFromLinearRGB(pixel, 1);
        }
        float[] rgb = getDefaultRGBComponents(pixel);
        return (int)(rgb[1] * 255.0F + 0.5F);
    }
    
    public final int getBlue(int pixel) {
        if (is_sRGB) {
            return getsRGBComponentFromsRGB(pixel, 2);
        } else if (is_LinearRGB) {
            return getsRGBComponentFromLinearRGB(pixel, 2);
        }
        float[] rgb = getDefaultRGBComponents(pixel);
        return (int)(rgb[2] * 255.0F + 0.5F);
    }
    
    public final int getAlpha(int pixel) {
        if (!supportsAlpha) return 255;
        int a = ((pixel & maskArray[3]) >>> maskOffsets[3]);
        if (scaleFactors[3] != 1.0F) {
            a = (int)(a * scaleFactors[3] + 0.5F);
        }
        return a;
    }
    
    public final int getRGB(int pixel) {
        if (is_sRGB || is_LinearRGB) {
            return (getAlpha(pixel) << 24) | (getRed(pixel) << 16) | (getGreen(pixel) << 8) | (getBlue(pixel) << 0);
        }
        float[] rgb = getDefaultRGBComponents(pixel);
        return (getAlpha(pixel) << 24) | (((int)(rgb[0] * 255.0F + 0.5F)) << 16) | (((int)(rgb[1] * 255.0F + 0.5F)) << 8) | (((int)(rgb[2] * 255.0F + 0.5F)) << 0);
    }
    
    public int getRed(Object inData) {
        int pixel = 0;
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            byte[] bdata = (byte[])(byte[])inData;
            pixel = bdata[0] & 255;
            break;
        
        case DataBuffer.TYPE_USHORT: 
            short[] sdata = (short[])(short[])inData;
            pixel = sdata[0] & 65535;
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] idata = (int[])(int[])inData;
            pixel = idata[0];
            break;
        
        default: 
            throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
        
        }
        return getRed(pixel);
    }
    
    public int getGreen(Object inData) {
        int pixel = 0;
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            byte[] bdata = (byte[])(byte[])inData;
            pixel = bdata[0] & 255;
            break;
        
        case DataBuffer.TYPE_USHORT: 
            short[] sdata = (short[])(short[])inData;
            pixel = sdata[0] & 65535;
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] idata = (int[])(int[])inData;
            pixel = idata[0];
            break;
        
        default: 
            throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
        
        }
        return getGreen(pixel);
    }
    
    public int getBlue(Object inData) {
        int pixel = 0;
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            byte[] bdata = (byte[])(byte[])inData;
            pixel = bdata[0] & 255;
            break;
        
        case DataBuffer.TYPE_USHORT: 
            short[] sdata = (short[])(short[])inData;
            pixel = sdata[0] & 65535;
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] idata = (int[])(int[])inData;
            pixel = idata[0];
            break;
        
        default: 
            throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
        
        }
        return getBlue(pixel);
    }
    
    public int getAlpha(Object inData) {
        int pixel = 0;
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            byte[] bdata = (byte[])(byte[])inData;
            pixel = bdata[0] & 255;
            break;
        
        case DataBuffer.TYPE_USHORT: 
            short[] sdata = (short[])(short[])inData;
            pixel = sdata[0] & 65535;
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] idata = (int[])(int[])inData;
            pixel = idata[0];
            break;
        
        default: 
            throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
        
        }
        return getAlpha(pixel);
    }
    
    public int getRGB(Object inData) {
        int pixel = 0;
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            byte[] bdata = (byte[])(byte[])inData;
            pixel = bdata[0] & 255;
            break;
        
        case DataBuffer.TYPE_USHORT: 
            short[] sdata = (short[])(short[])inData;
            pixel = sdata[0] & 65535;
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] idata = (int[])(int[])inData;
            pixel = idata[0];
            break;
        
        default: 
            throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
        
        }
        return getRGB(pixel);
    }
    
    public Object getDataElements(int rgb, Object pixel) {
        int[] intpixel = null;
        if (transferType == DataBuffer.TYPE_INT && pixel != null) {
            intpixel = (int[])(int[])pixel;
            intpixel[0] = 0;
        } else {
            intpixel = new int[1];
        }
        ColorModel defaultCM = ColorModel.getRGBdefault();
        if (this == defaultCM || equals(defaultCM)) {
            intpixel[0] = rgb;
            return intpixel;
        }
        int red;
        int grn;
        int blu;
        int alp;
        red = (rgb >> 16) & 255;
        grn = (rgb >> 8) & 255;
        blu = rgb & 255;
        if (is_sRGB || is_LinearRGB) {
            int precision;
            float factor;
            if (is_LinearRGB) {
                if (lRGBprecision == 8) {
                    red = fromsRGB8LUT8[red] & 255;
                    grn = fromsRGB8LUT8[grn] & 255;
                    blu = fromsRGB8LUT8[blu] & 255;
                    precision = 8;
                    factor = 1.0F / 255.0F;
                } else {
                    red = fromsRGB8LUT16[red] & 65535;
                    grn = fromsRGB8LUT16[grn] & 65535;
                    blu = fromsRGB8LUT16[blu] & 65535;
                    precision = 16;
                    factor = 1.0F / 65535.0F;
                }
            } else {
                precision = 8;
                factor = 1.0F / 255.0F;
            }
            if (supportsAlpha) {
                alp = (rgb >> 24) & 255;
                if (isAlphaPremultiplied) {
                    factor *= (alp * (1.0F / 255.0F));
                    precision = -1;
                }
                if (nBits[3] != 8) {
                    alp = (int)((alp * (1.0F / 255.0F) * ((1 << nBits[3]) - 1)) + 0.5F);
                    if (alp > ((1 << nBits[3]) - 1)) {
                        alp = (1 << nBits[3]) - 1;
                    }
                }
                intpixel[0] = alp << maskOffsets[3];
            }
            if (nBits[0] != precision) {
                red = (int)((red * factor * ((1 << nBits[0]) - 1)) + 0.5F);
            }
            if (nBits[1] != precision) {
                grn = (int)((grn * factor * ((1 << nBits[1]) - 1)) + 0.5F);
            }
            if (nBits[2] != precision) {
                blu = (int)((blu * factor * ((1 << nBits[2]) - 1)) + 0.5F);
            }
        } else {
            float[] norm = new float[3];
            float factor = 1.0F / 255.0F;
            norm[0] = red * factor;
            norm[1] = grn * factor;
            norm[2] = blu * factor;
            norm = colorSpace.fromRGB(norm);
            if (supportsAlpha) {
                alp = (rgb >> 24) & 255;
                if (isAlphaPremultiplied) {
                    factor *= alp;
                    for (int i = 0; i < 3; i++) {
                        norm[i] *= factor;
                    }
                }
                if (nBits[3] != 8) {
                    alp = (int)((alp * (1.0F / 255.0F) * ((1 << nBits[3]) - 1)) + 0.5F);
                    if (alp > ((1 << nBits[3]) - 1)) {
                        alp = (1 << nBits[3]) - 1;
                    }
                }
                intpixel[0] = alp << maskOffsets[3];
            }
            red = (int)((norm[0] * ((1 << nBits[0]) - 1)) + 0.5F);
            grn = (int)((norm[1] * ((1 << nBits[1]) - 1)) + 0.5F);
            blu = (int)((norm[2] * ((1 << nBits[2]) - 1)) + 0.5F);
        }
        if (maxBits > 23) {
            if (red > ((1 << nBits[0]) - 1)) {
                red = (1 << nBits[0]) - 1;
            }
            if (grn > ((1 << nBits[1]) - 1)) {
                grn = (1 << nBits[1]) - 1;
            }
            if (blu > ((1 << nBits[2]) - 1)) {
                blu = (1 << nBits[2]) - 1;
            }
        }
        intpixel[0] |= (red << maskOffsets[0]) | (grn << maskOffsets[1]) | (blu << maskOffsets[2]);
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            {
                byte[] bdata;
                if (pixel == null) {
                    bdata = new byte[1];
                } else {
                    bdata = (byte[])(byte[])pixel;
                }
                bdata[0] = (byte)(255 & intpixel[0]);
                return bdata;
            }
        
        case DataBuffer.TYPE_USHORT: 
            {
                short[] sdata;
                if (pixel == null) {
                    sdata = new short[1];
                } else {
                    sdata = (short[])(short[])pixel;
                }
                sdata[0] = (short)(intpixel[0] & 65535);
                return sdata;
            }
        
        case DataBuffer.TYPE_INT: 
            return intpixel;
        
        }
        throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
    }
    
    public final int[] getComponents(int pixel, int[] components, int offset) {
        if (components == null) {
            components = new int[offset + numComponents];
        }
        for (int i = 0; i < numComponents; i++) {
            components[offset + i] = (pixel & maskArray[i]) >>> maskOffsets[i];
        }
        return components;
    }
    
    public final int[] getComponents(Object pixel, int[] components, int offset) {
        int intpixel = 0;
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
    
    public final WritableRaster createCompatibleWritableRaster(int w, int h) {
        if ((w <= 0) || (h <= 0)) {
            throw new IllegalArgumentException("Width (" + w + ") and height (" + h + ") cannot be <= 0");
        }
        int[] bandmasks;
        if (supportsAlpha) {
            bandmasks = new int[4];
            bandmasks[3] = alpha_mask;
        } else {
            bandmasks = new int[3];
        }
        bandmasks[0] = red_mask;
        bandmasks[1] = green_mask;
        bandmasks[2] = blue_mask;
        if (pixel_bits > 16) {
            return Raster.createPackedRaster(DataBuffer.TYPE_INT, w, h, bandmasks, null);
        } else if (pixel_bits > 8) {
            return Raster.createPackedRaster(DataBuffer.TYPE_USHORT, w, h, bandmasks, null);
        } else {
            return Raster.createPackedRaster(DataBuffer.TYPE_BYTE, w, h, bandmasks, null);
        }
    }
    
    public int getDataElement(int[] components, int offset) {
        int pixel = 0;
        for (int i = 0; i < numComponents; i++) {
            pixel |= ((components[offset + i] << maskOffsets[i]) & maskArray[i]);
        }
        return pixel;
    }
    
    public Object getDataElements(int[] components, int offset, Object obj) {
        int pixel = 0;
        for (int i = 0; i < numComponents; i++) {
            pixel |= ((components[offset + i] << maskOffsets[i]) & maskArray[i]);
        }
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            if (obj instanceof byte[]) {
                byte[] bdata = (byte[])(byte[])obj;
                bdata[0] = (byte)(pixel & 255);
                return bdata;
            } else {
                byte[] bdata = {(byte)(pixel & 255)};
                return bdata;
            }
        
        case DataBuffer.TYPE_USHORT: 
            if (obj instanceof short[]) {
                short[] sdata = (short[])(short[])obj;
                sdata[0] = (short)(pixel & 65535);
                return sdata;
            } else {
                short[] sdata = {(short)(pixel & 65535)};
                return sdata;
            }
        
        case DataBuffer.TYPE_INT: 
            if (obj instanceof int[]) {
                int[] idata = (int[])(int[])obj;
                idata[0] = pixel;
                return idata;
            } else {
                int[] idata = {pixel};
                return idata;
            }
        
        default: 
            throw new ClassCastException("This method has not been " + "implemented for transferType " + transferType);
        
        }
    }
    
    public final ColorModel coerceData(WritableRaster raster, boolean isAlphaPremultiplied) {
        if (!supportsAlpha || this.isAlphaPremultiplied() == isAlphaPremultiplied) {
            return this;
        }
        int w = raster.getWidth();
        int h = raster.getHeight();
        int aIdx = numColorComponents;
        float normAlpha;
        float alphaScale = 1.0F / ((float)((1 << nBits[aIdx]) - 1));
        int rminX = raster.getMinX();
        int rY = raster.getMinY();
        int rX;
        int[] pixel = null;
        int[] zpixel = null;
        if (isAlphaPremultiplied) {
            switch (transferType) {
            case DataBuffer.TYPE_BYTE: 
                {
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = raster.getPixel(rX, rY, pixel);
                            normAlpha = pixel[aIdx] * alphaScale;
                            if (normAlpha != 0.0F) {
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] = (int)(pixel[c] * normAlpha + 0.5F);
                                }
                                raster.setPixel(rX, rY, pixel);
                            } else {
                                if (zpixel == null) {
                                    zpixel = new int[numComponents];
                                    java.util.Arrays.fill(zpixel, 0);
                                }
                                raster.setPixel(rX, rY, zpixel);
                            }
                        }
                    }
                }
                break;
            
            case DataBuffer.TYPE_USHORT: 
                {
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = raster.getPixel(rX, rY, pixel);
                            normAlpha = pixel[aIdx] * alphaScale;
                            if (normAlpha != 0.0F) {
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] = (int)(pixel[c] * normAlpha + 0.5F);
                                }
                                raster.setPixel(rX, rY, pixel);
                            } else {
                                if (zpixel == null) {
                                    zpixel = new int[numComponents];
                                    java.util.Arrays.fill(zpixel, 0);
                                }
                                raster.setPixel(rX, rY, zpixel);
                            }
                        }
                    }
                }
                break;
            
            case DataBuffer.TYPE_INT: 
                {
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = raster.getPixel(rX, rY, pixel);
                            normAlpha = pixel[aIdx] * alphaScale;
                            if (normAlpha != 0.0F) {
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] = (int)(pixel[c] * normAlpha + 0.5F);
                                }
                                raster.setPixel(rX, rY, pixel);
                            } else {
                                if (zpixel == null) {
                                    zpixel = new int[numComponents];
                                    java.util.Arrays.fill(zpixel, 0);
                                }
                                raster.setPixel(rX, rY, zpixel);
                            }
                        }
                    }
                }
                break;
            
            default: 
                throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
            
            }
        } else {
            switch (transferType) {
            case DataBuffer.TYPE_BYTE: 
                {
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = raster.getPixel(rX, rY, pixel);
                            normAlpha = pixel[aIdx] * alphaScale;
                            if (normAlpha != 0.0F) {
                                float invAlpha = 1.0F / normAlpha;
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] = (int)(pixel[c] * invAlpha + 0.5F);
                                }
                                raster.setPixel(rX, rY, pixel);
                            }
                        }
                    }
                }
                break;
            
            case DataBuffer.TYPE_USHORT: 
                {
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = raster.getPixel(rX, rY, pixel);
                            normAlpha = pixel[aIdx] * alphaScale;
                            if (normAlpha != 0) {
                                float invAlpha = 1.0F / normAlpha;
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] = (int)(pixel[c] * invAlpha + 0.5F);
                                }
                                raster.setPixel(rX, rY, pixel);
                            }
                        }
                    }
                }
                break;
            
            case DataBuffer.TYPE_INT: 
                {
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = raster.getPixel(rX, rY, pixel);
                            normAlpha = pixel[aIdx] * alphaScale;
                            if (normAlpha != 0) {
                                float invAlpha = 1.0F / normAlpha;
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] = (int)(pixel[c] * invAlpha + 0.5F);
                                }
                                raster.setPixel(rX, rY, pixel);
                            }
                        }
                    }
                }
                break;
            
            default: 
                throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
            
            }
        }
        return new DirectColorModel(colorSpace, pixel_bits, maskArray[0], maskArray[1], maskArray[2], maskArray[3], isAlphaPremultiplied, transferType);
    }
    
    public boolean isCompatibleRaster(Raster raster) {
        SampleModel sm = raster.getSampleModel();
        SinglePixelPackedSampleModel spsm;
        if (sm instanceof SinglePixelPackedSampleModel) {
            spsm = (SinglePixelPackedSampleModel)(SinglePixelPackedSampleModel)sm;
        } else {
            return false;
        }
        if (spsm.getNumBands() != getNumComponents()) {
            return false;
        }
        int[] bitMasks = spsm.getBitMasks();
        for (int i = 0; i < numComponents; i++) {
            if (bitMasks[i] != maskArray[i]) {
                return false;
            }
        }
        return (raster.getTransferType() == transferType);
    }
    
    private void setFields() {
        red_mask = maskArray[0];
        red_offset = maskOffsets[0];
        green_mask = maskArray[1];
        green_offset = maskOffsets[1];
        blue_mask = maskArray[2];
        blue_offset = maskOffsets[2];
        if (nBits[0] < 8) {
            red_scale = (1 << nBits[0]) - 1;
        }
        if (nBits[1] < 8) {
            green_scale = (1 << nBits[1]) - 1;
        }
        if (nBits[2] < 8) {
            blue_scale = (1 << nBits[2]) - 1;
        }
        if (supportsAlpha) {
            alpha_mask = maskArray[3];
            alpha_offset = maskOffsets[3];
            if (nBits[3] < 8) {
                alpha_scale = (1 << nBits[3]) - 1;
            }
        }
    }
    
    public String toString() {
        return new String("DirectColorModel: rmask=" + Integer.toHexString(red_mask) + " gmask=" + Integer.toHexString(green_mask) + " bmask=" + Integer.toHexString(blue_mask) + " amask=" + Integer.toHexString(alpha_mask));
    }
}
