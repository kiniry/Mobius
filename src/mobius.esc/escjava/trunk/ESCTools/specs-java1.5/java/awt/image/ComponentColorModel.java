package java.awt.image;

import java.awt.color.ColorSpace;
import java.awt.color.ICC_ColorSpace;

public class ComponentColorModel extends ColorModel {
    private boolean signed;
    private boolean is_sRGB_stdScale;
    private boolean is_LinearRGB_stdScale;
    private boolean is_LinearGray_stdScale;
    private boolean is_ICCGray_stdScale;
    private byte[] tosRGB8LUT;
    private byte[] fromsRGB8LUT8;
    private short[] fromsRGB8LUT16;
    private byte[] fromLinearGray16ToOtherGray8LUT;
    private short[] fromLinearGray16ToOtherGray16LUT;
    private boolean needScaleInit;
    private boolean noUnnorm;
    private boolean nonStdScale;
    private float[] min;
    private float[] diffMinMax;
    private float[] compOffset;
    private float[] compScale;
    
    public ComponentColorModel(ColorSpace colorSpace, int[] bits, boolean hasAlpha, boolean isAlphaPremultiplied, int transparency, int transferType) {
        super(bitsHelper(transferType, colorSpace, hasAlpha), bitsArrayHelper(bits, transferType, colorSpace, hasAlpha), colorSpace, hasAlpha, isAlphaPremultiplied, transparency, transferType);
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
        
        case DataBuffer.TYPE_USHORT: 
        
        case DataBuffer.TYPE_INT: 
            signed = false;
            needScaleInit = true;
            break;
        
        case DataBuffer.TYPE_SHORT: 
            signed = true;
            needScaleInit = true;
            break;
        
        case DataBuffer.TYPE_FLOAT: 
        
        case DataBuffer.TYPE_DOUBLE: 
            signed = true;
            needScaleInit = false;
            noUnnorm = true;
            nonStdScale = false;
            break;
        
        default: 
            throw new IllegalArgumentException("This constructor is not " + "compatible with transferType " + transferType);
        
        }
        setupLUTs();
    }
    
    public ComponentColorModel(ColorSpace colorSpace, boolean hasAlpha, boolean isAlphaPremultiplied, int transparency, int transferType) {
        this(colorSpace, null, hasAlpha, isAlphaPremultiplied, transparency, transferType);
    }
    
    private static int bitsHelper(int transferType, ColorSpace colorSpace, boolean hasAlpha) {
        int numBits = DataBuffer.getDataTypeSize(transferType);
        int numComponents = colorSpace.getNumComponents();
        if (hasAlpha) {
            ++numComponents;
        }
        return numBits * numComponents;
    }
    
    private static int[] bitsArrayHelper(int[] origBits, int transferType, ColorSpace colorSpace, boolean hasAlpha) {
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
        
        case DataBuffer.TYPE_USHORT: 
        
        case DataBuffer.TYPE_INT: 
            if (origBits != null) {
                return origBits;
            }
            break;
        
        default: 
            break;
        
        }
        int numBits = DataBuffer.getDataTypeSize(transferType);
        int numComponents = colorSpace.getNumComponents();
        if (hasAlpha) {
            ++numComponents;
        }
        int[] bits = new int[numComponents];
        for (int i = 0; i < numComponents; i++) {
            bits[i] = numBits;
        }
        return bits;
    }
    
    private void setupLUTs() {
        if (is_sRGB) {
            is_sRGB_stdScale = true;
            nonStdScale = false;
        } else if (ColorModel.isLinearRGBspace(colorSpace)) {
            is_LinearRGB_stdScale = true;
            nonStdScale = false;
            if (transferType == DataBuffer.TYPE_BYTE) {
                tosRGB8LUT = ColorModel.getLinearRGB8TosRGB8LUT();
                fromsRGB8LUT8 = ColorModel.getsRGB8ToLinearRGB8LUT();
            } else {
                tosRGB8LUT = ColorModel.getLinearRGB16TosRGB8LUT();
                fromsRGB8LUT16 = ColorModel.getsRGB8ToLinearRGB16LUT();
            }
        } else if ((colorSpaceType == ColorSpace.TYPE_GRAY) && (colorSpace instanceof ICC_ColorSpace) && (colorSpace.getMinValue(0) == 0.0F) && (colorSpace.getMaxValue(0) == 1.0F)) {
            ICC_ColorSpace ics = (ICC_ColorSpace)(ICC_ColorSpace)colorSpace;
            is_ICCGray_stdScale = true;
            nonStdScale = false;
            fromsRGB8LUT16 = ColorModel.getsRGB8ToLinearRGB16LUT();
            if (ColorModel.isLinearGRAYspace(ics)) {
                is_LinearGray_stdScale = true;
                if (transferType == DataBuffer.TYPE_BYTE) {
                    tosRGB8LUT = ColorModel.getGray8TosRGB8LUT(ics);
                } else {
                    tosRGB8LUT = ColorModel.getGray16TosRGB8LUT(ics);
                }
            } else {
                if (transferType == DataBuffer.TYPE_BYTE) {
                    tosRGB8LUT = ColorModel.getGray8TosRGB8LUT(ics);
                    fromLinearGray16ToOtherGray8LUT = ColorModel.getLinearGray16ToOtherGray8LUT(ics);
                } else {
                    tosRGB8LUT = ColorModel.getGray16TosRGB8LUT(ics);
                    fromLinearGray16ToOtherGray16LUT = ColorModel.getLinearGray16ToOtherGray16LUT(ics);
                }
            }
        } else if (needScaleInit) {
            nonStdScale = false;
            for (int i = 0; i < numColorComponents; i++) {
                if ((colorSpace.getMinValue(i) != 0.0F) || (colorSpace.getMaxValue(i) != 1.0F)) {
                    nonStdScale = true;
                    break;
                }
            }
            if (nonStdScale) {
                min = new float[numColorComponents];
                diffMinMax = new float[numColorComponents];
                for (int i = 0; i < numColorComponents; i++) {
                    min[i] = colorSpace.getMinValue(i);
                    diffMinMax[i] = colorSpace.getMaxValue(i) - min[i];
                }
            }
        }
    }
    
    private void initScale() {
        needScaleInit = false;
        if (nonStdScale || signed) {
            noUnnorm = true;
        } else {
            noUnnorm = false;
        }
        float[] lowVal;
        float[] highVal;
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            {
                byte[] bpixel = new byte[numComponents];
                for (int i = 0; i < numColorComponents; i++) {
                    bpixel[i] = 0;
                }
                if (supportsAlpha) {
                    bpixel[numColorComponents] = (byte)((1 << nBits[numColorComponents]) - 1);
                }
                lowVal = getNormalizedComponents(bpixel, null, 0);
                for (int i = 0; i < numColorComponents; i++) {
                    bpixel[i] = (byte)((1 << nBits[i]) - 1);
                }
                highVal = getNormalizedComponents(bpixel, null, 0);
            }
            break;
        
        case DataBuffer.TYPE_USHORT: 
            {
                short[] uspixel = new short[numComponents];
                for (int i = 0; i < numColorComponents; i++) {
                    uspixel[i] = 0;
                }
                if (supportsAlpha) {
                    uspixel[numColorComponents] = (short)((1 << nBits[numColorComponents]) - 1);
                }
                lowVal = getNormalizedComponents(uspixel, null, 0);
                for (int i = 0; i < numColorComponents; i++) {
                    uspixel[i] = (short)((1 << nBits[i]) - 1);
                }
                highVal = getNormalizedComponents(uspixel, null, 0);
            }
            break;
        
        case DataBuffer.TYPE_INT: 
            {
                int[] ipixel = new int[numComponents];
                for (int i = 0; i < numColorComponents; i++) {
                    ipixel[i] = 0;
                }
                if (supportsAlpha) {
                    ipixel[numColorComponents] = ((1 << nBits[numColorComponents]) - 1);
                }
                lowVal = getNormalizedComponents(ipixel, null, 0);
                for (int i = 0; i < numColorComponents; i++) {
                    ipixel[i] = ((1 << nBits[i]) - 1);
                }
                highVal = getNormalizedComponents(ipixel, null, 0);
            }
            break;
        
        case DataBuffer.TYPE_SHORT: 
            {
                short[] spixel = new short[numComponents];
                for (int i = 0; i < numColorComponents; i++) {
                    spixel[i] = 0;
                }
                if (supportsAlpha) {
                    spixel[numColorComponents] = 32767;
                }
                lowVal = getNormalizedComponents(spixel, null, 0);
                for (int i = 0; i < numColorComponents; i++) {
                    spixel[i] = 32767;
                }
                highVal = getNormalizedComponents(spixel, null, 0);
            }
            break;
        
        default: 
            lowVal = highVal = null;
            break;
        
        }
        nonStdScale = false;
        for (int i = 0; i < numColorComponents; i++) {
            if ((lowVal[i] != 0.0F) || (highVal[i] != 1.0F)) {
                nonStdScale = true;
                break;
            }
        }
        if (nonStdScale) {
            noUnnorm = true;
            is_sRGB_stdScale = false;
            is_LinearRGB_stdScale = false;
            is_LinearGray_stdScale = false;
            is_ICCGray_stdScale = false;
            compOffset = new float[numColorComponents];
            compScale = new float[numColorComponents];
            for (int i = 0; i < numColorComponents; i++) {
                compOffset[i] = lowVal[i];
                compScale[i] = 1.0F / (highVal[i] - lowVal[i]);
            }
        }
    }
    
    private int getRGBComponent(int pixel, int idx) {
        if (numComponents > 1) {
            throw new IllegalArgumentException("More than one component per pixel");
        }
        if (signed) {
            throw new IllegalArgumentException("Component value is signed");
        }
        if (needScaleInit) {
            initScale();
        }
        Object opixel = null;
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            {
                byte[] bpixel = {(byte)pixel};
                opixel = bpixel;
            }
            break;
        
        case DataBuffer.TYPE_USHORT: 
            {
                short[] spixel = {(short)pixel};
                opixel = spixel;
            }
            break;
        
        case DataBuffer.TYPE_INT: 
            {
                int[] ipixel = {pixel};
                opixel = ipixel;
            }
            break;
        
        }
        float[] norm = getNormalizedComponents(opixel, null, 0);
        float[] rgb = colorSpace.toRGB(norm);
        return (int)(rgb[idx] * 255.0F + 0.5F);
    }
    
    public int getRed(int pixel) {
        return getRGBComponent(pixel, 0);
    }
    
    public int getGreen(int pixel) {
        return getRGBComponent(pixel, 1);
    }
    
    public int getBlue(int pixel) {
        return getRGBComponent(pixel, 2);
    }
    
    public int getAlpha(int pixel) {
        if (supportsAlpha == false) {
            return 255;
        }
        if (numComponents > 1) {
            throw new IllegalArgumentException("More than one component per pixel");
        }
        if (signed) {
            throw new IllegalArgumentException("Component value is signed");
        }
        return (int)((((float)pixel) / ((1 << nBits[0]) - 1)) * 255.0F + 0.5F);
    }
    
    public int getRGB(int pixel) {
        if (numComponents > 1) {
            throw new IllegalArgumentException("More than one component per pixel");
        }
        if (signed) {
            throw new IllegalArgumentException("Component value is signed");
        }
        return (getAlpha(pixel) << 24) | (getRed(pixel) << 16) | (getGreen(pixel) << 8) | (getBlue(pixel) << 0);
    }
    
    private int extractComponent(Object inData, int idx, int precision) {
        boolean needAlpha = (supportsAlpha && isAlphaPremultiplied);
        int alp = 0;
        int comp;
        int mask = (1 << nBits[idx]) - 1;
        switch (transferType) {
        case DataBuffer.TYPE_SHORT: 
            {
                short[] sdata = (short[])(short[])inData;
                float scalefactor = (float)((1 << precision) - 1);
                if (needAlpha) {
                    short s = sdata[numColorComponents];
                    if (s != (short)0) {
                        return (int)((((float)sdata[idx]) / ((float)s)) * scalefactor + 0.5F);
                    } else {
                        return 0;
                    }
                } else {
                    return (int)((sdata[idx] / 32767.0F) * scalefactor + 0.5F);
                }
            }
        
        case DataBuffer.TYPE_FLOAT: 
            {
                float[] fdata = (float[])(float[])inData;
                float scalefactor = (float)((1 << precision) - 1);
                if (needAlpha) {
                    float f = fdata[numColorComponents];
                    if (f != 0.0F) {
                        return (int)(((fdata[idx] / f) * scalefactor) + 0.5F);
                    } else {
                        return 0;
                    }
                } else {
                    return (int)(fdata[idx] * scalefactor + 0.5F);
                }
            }
        
        case DataBuffer.TYPE_DOUBLE: 
            {
                double[] ddata = (double[])(double[])inData;
                double scalefactor = (double)((1 << precision) - 1);
                if (needAlpha) {
                    double d = ddata[numColorComponents];
                    if (d != 0.0) {
                        return (int)(((ddata[idx] / d) * scalefactor) + 0.5);
                    } else {
                        return 0;
                    }
                } else {
                    return (int)(ddata[idx] * scalefactor + 0.5);
                }
            }
        
        case DataBuffer.TYPE_BYTE: 
            byte[] bdata = (byte[])(byte[])inData;
            comp = bdata[idx] & mask;
            precision = 8;
            if (needAlpha) {
                alp = bdata[numColorComponents] & mask;
            }
            break;
        
        case DataBuffer.TYPE_USHORT: 
            short[] usdata = (short[])(short[])inData;
            comp = usdata[idx] & mask;
            if (needAlpha) {
                alp = usdata[numColorComponents] & mask;
            }
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] idata = (int[])(int[])inData;
            comp = idata[idx];
            if (needAlpha) {
                alp = idata[numColorComponents];
            }
            break;
        
        default: 
            throw new UnsupportedOperationException("This method has not " + "been implemented for transferType " + transferType);
        
        }
        if (needAlpha) {
            if (alp != 0) {
                float scalefactor = (float)((1 << precision) - 1);
                float fcomp = ((float)comp) / ((float)mask);
                float invalp = ((float)((1 << nBits[numColorComponents]) - 1)) / ((float)alp);
                return (int)(fcomp * invalp * scalefactor + 0.5F);
            } else {
                return 0;
            }
        } else {
            if (nBits[idx] != precision) {
                float scalefactor = (float)((1 << precision) - 1);
                float fcomp = ((float)comp) / ((float)mask);
                return (int)(fcomp * scalefactor + 0.5F);
            }
            return comp;
        }
    }
    
    private int getRGBComponent(Object inData, int idx) {
        if (needScaleInit) {
            initScale();
        }
        if (is_sRGB_stdScale) {
            return extractComponent(inData, idx, 8);
        } else if (is_LinearRGB_stdScale) {
            int lutidx = extractComponent(inData, idx, 16);
            return tosRGB8LUT[lutidx] & 255;
        } else if (is_ICCGray_stdScale) {
            int lutidx = extractComponent(inData, 0, 16);
            return tosRGB8LUT[lutidx] & 255;
        }
        float[] norm = getNormalizedComponents(inData, null, 0);
        float[] rgb = colorSpace.toRGB(norm);
        return (int)(rgb[idx] * 255.0F + 0.5F);
    }
    
    public int getRed(Object inData) {
        return getRGBComponent(inData, 0);
    }
    
    public int getGreen(Object inData) {
        return getRGBComponent(inData, 1);
    }
    
    public int getBlue(Object inData) {
        return getRGBComponent(inData, 2);
    }
    
    public int getAlpha(Object inData) {
        if (supportsAlpha == false) {
            return 255;
        }
        int alpha = 0;
        int aIdx = numColorComponents;
        int mask = (1 << nBits[aIdx]) - 1;
        switch (transferType) {
        case DataBuffer.TYPE_SHORT: 
            short[] sdata = (short[])(short[])inData;
            alpha = (int)((sdata[aIdx] / 32767.0F) * 255.0F + 0.5F);
            return alpha;
        
        case DataBuffer.TYPE_FLOAT: 
            float[] fdata = (float[])(float[])inData;
            alpha = (int)(fdata[aIdx] * 255.0F + 0.5F);
            return alpha;
        
        case DataBuffer.TYPE_DOUBLE: 
            double[] ddata = (double[])(double[])inData;
            alpha = (int)(ddata[aIdx] * 255.0 + 0.5);
            return alpha;
        
        case DataBuffer.TYPE_BYTE: 
            byte[] bdata = (byte[])(byte[])inData;
            alpha = bdata[aIdx] & mask;
            break;
        
        case DataBuffer.TYPE_USHORT: 
            short[] usdata = (short[])(short[])inData;
            alpha = usdata[aIdx] & mask;
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] idata = (int[])(int[])inData;
            alpha = idata[aIdx];
            break;
        
        default: 
            throw new UnsupportedOperationException("This method has not " + "been implemented for transferType " + transferType);
        
        }
        if (nBits[aIdx] == 8) {
            return alpha;
        } else {
            return (int)((((float)alpha) / ((float)((1 << nBits[aIdx]) - 1))) * 255.0F + 0.5F);
        }
    }
    
    public int getRGB(Object inData) {
        if (needScaleInit) {
            initScale();
        }
        if (is_sRGB_stdScale || is_LinearRGB_stdScale) {
            return (getAlpha(inData) << 24) | (getRed(inData) << 16) | (getGreen(inData) << 8) | (getBlue(inData));
        } else if (colorSpaceType == ColorSpace.TYPE_GRAY) {
            int gray = getRed(inData);
            return (getAlpha(inData) << 24) | (gray << 16) | (gray << 8) | gray;
        }
        float[] norm = getNormalizedComponents(inData, null, 0);
        float[] rgb = colorSpace.toRGB(norm);
        return (getAlpha(inData) << 24) | (((int)(rgb[0] * 255.0F + 0.5F)) << 16) | (((int)(rgb[1] * 255.0F + 0.5F)) << 8) | (((int)(rgb[2] * 255.0F + 0.5F)) << 0);
    }
    
    public Object getDataElements(int rgb, Object pixel) {
        int red;
        int grn;
        int blu;
        int alp;
        red = (rgb >> 16) & 255;
        grn = (rgb >> 8) & 255;
        blu = rgb & 255;
        if (needScaleInit) {
            initScale();
        }
        if (signed) {
            switch (transferType) {
            case DataBuffer.TYPE_SHORT: 
                {
                    short[] sdata;
                    if (pixel == null) {
                        sdata = new short[numComponents];
                    } else {
                        sdata = (short[])(short[])pixel;
                    }
                    float factor;
                    if (is_sRGB_stdScale || is_LinearRGB_stdScale) {
                        factor = 32767.0F / 255.0F;
                        if (is_LinearRGB_stdScale) {
                            red = fromsRGB8LUT16[red] & 65535;
                            grn = fromsRGB8LUT16[grn] & 65535;
                            blu = fromsRGB8LUT16[blu] & 65535;
                            factor = 32767.0F / 65535.0F;
                        }
                        if (supportsAlpha) {
                            alp = (rgb >> 24) & 255;
                            sdata[3] = (short)(alp * (32767.0F / 255.0F) + 0.5F);
                            if (isAlphaPremultiplied) {
                                factor = alp * factor * (1.0F / 255.0F);
                            }
                        }
                        sdata[0] = (short)(red * factor + 0.5F);
                        sdata[1] = (short)(grn * factor + 0.5F);
                        sdata[2] = (short)(blu * factor + 0.5F);
                    } else if (is_LinearGray_stdScale) {
                        red = fromsRGB8LUT16[red] & 65535;
                        grn = fromsRGB8LUT16[grn] & 65535;
                        blu = fromsRGB8LUT16[blu] & 65535;
                        float gray = ((0.2125F * red) + (0.7154F * grn) + (0.0721F * blu)) / 65535.0F;
                        factor = 32767.0F;
                        if (supportsAlpha) {
                            alp = (rgb >> 24) & 255;
                            sdata[1] = (short)(alp * (32767.0F / 255.0F) + 0.5F);
                            if (isAlphaPremultiplied) {
                                factor = alp * factor * (1.0F / 255.0F);
                            }
                        }
                        sdata[0] = (short)(gray * factor + 0.5F);
                    } else if (is_ICCGray_stdScale) {
                        red = fromsRGB8LUT16[red] & 65535;
                        grn = fromsRGB8LUT16[grn] & 65535;
                        blu = fromsRGB8LUT16[blu] & 65535;
                        int gray = (int)((0.2125F * red) + (0.7154F * grn) + (0.0721F * blu) + 0.5F);
                        gray = fromLinearGray16ToOtherGray16LUT[gray] & 65535;
                        factor = 32767.0F / 65535.0F;
                        if (supportsAlpha) {
                            alp = (rgb >> 24) & 255;
                            sdata[1] = (short)(alp * (32767.0F / 255.0F) + 0.5F);
                            if (isAlphaPremultiplied) {
                                factor = alp * factor * (1.0F / 255.0F);
                            }
                        }
                        sdata[0] = (short)(gray * factor + 0.5F);
                    } else {
                        factor = 1.0F / 255.0F;
                        float[] norm = new float[3];
                        norm[0] = red * factor;
                        norm[1] = grn * factor;
                        norm[2] = blu * factor;
                        norm = colorSpace.fromRGB(norm);
                        if (nonStdScale) {
                            for (int i = 0; i < numColorComponents; i++) {
                                norm[i] = (norm[i] - compOffset[i]) * compScale[i];
                                if (norm[i] < 0.0F) {
                                    norm[i] = 0.0F;
                                }
                                if (norm[i] > 1.0F) {
                                    norm[i] = 1.0F;
                                }
                            }
                        }
                        factor = 32767.0F;
                        if (supportsAlpha) {
                            alp = (rgb >> 24) & 255;
                            sdata[numColorComponents] = (short)(alp * (32767.0F / 255.0F) + 0.5F);
                            if (isAlphaPremultiplied) {
                                factor *= alp * (1.0F / 255.0F);
                            }
                        }
                        for (int i = 0; i < numColorComponents; i++) {
                            sdata[i] = (short)(norm[i] * factor + 0.5F);
                        }
                    }
                    return sdata;
                }
            
            case DataBuffer.TYPE_FLOAT: 
                {
                    float[] fdata;
                    if (pixel == null) {
                        fdata = new float[numComponents];
                    } else {
                        fdata = (float[])(float[])pixel;
                    }
                    float factor;
                    if (is_sRGB_stdScale || is_LinearRGB_stdScale) {
                        if (is_LinearRGB_stdScale) {
                            red = fromsRGB8LUT16[red] & 65535;
                            grn = fromsRGB8LUT16[grn] & 65535;
                            blu = fromsRGB8LUT16[blu] & 65535;
                            factor = 1.0F / 65535.0F;
                        } else {
                            factor = 1.0F / 255.0F;
                        }
                        if (supportsAlpha) {
                            alp = (rgb >> 24) & 255;
                            fdata[3] = alp * (1.0F / 255.0F);
                            if (isAlphaPremultiplied) {
                                factor *= fdata[3];
                            }
                        }
                        fdata[0] = red * factor;
                        fdata[1] = grn * factor;
                        fdata[2] = blu * factor;
                    } else if (is_LinearGray_stdScale) {
                        red = fromsRGB8LUT16[red] & 65535;
                        grn = fromsRGB8LUT16[grn] & 65535;
                        blu = fromsRGB8LUT16[blu] & 65535;
                        fdata[0] = ((0.2125F * red) + (0.7154F * grn) + (0.0721F * blu)) / 65535.0F;
                        if (supportsAlpha) {
                            alp = (rgb >> 24) & 255;
                            fdata[1] = alp * (1.0F / 255.0F);
                            if (isAlphaPremultiplied) {
                                fdata[0] *= fdata[1];
                            }
                        }
                    } else if (is_ICCGray_stdScale) {
                        red = fromsRGB8LUT16[red] & 65535;
                        grn = fromsRGB8LUT16[grn] & 65535;
                        blu = fromsRGB8LUT16[blu] & 65535;
                        int gray = (int)((0.2125F * red) + (0.7154F * grn) + (0.0721F * blu) + 0.5F);
                        fdata[0] = (fromLinearGray16ToOtherGray16LUT[gray] & 65535) / 65535.0F;
                        if (supportsAlpha) {
                            alp = (rgb >> 24) & 255;
                            fdata[1] = alp * (1.0F / 255.0F);
                            if (isAlphaPremultiplied) {
                                fdata[0] *= fdata[1];
                            }
                        }
                    } else {
                        float[] norm = new float[3];
                        factor = 1.0F / 255.0F;
                        norm[0] = red * factor;
                        norm[1] = grn * factor;
                        norm[2] = blu * factor;
                        norm = colorSpace.fromRGB(norm);
                        if (supportsAlpha) {
                            alp = (rgb >> 24) & 255;
                            fdata[numColorComponents] = alp * factor;
                            if (isAlphaPremultiplied) {
                                factor *= alp;
                                for (int i = 0; i < numColorComponents; i++) {
                                    norm[i] *= factor;
                                }
                            }
                        }
                        for (int i = 0; i < numColorComponents; i++) {
                            fdata[i] = norm[i];
                        }
                    }
                    return fdata;
                }
            
            case DataBuffer.TYPE_DOUBLE: 
                {
                    double[] ddata;
                    if (pixel == null) {
                        ddata = new double[numComponents];
                    } else {
                        ddata = (double[])(double[])pixel;
                    }
                    if (is_sRGB_stdScale || is_LinearRGB_stdScale) {
                        double factor;
                        if (is_LinearRGB_stdScale) {
                            red = fromsRGB8LUT16[red] & 65535;
                            grn = fromsRGB8LUT16[grn] & 65535;
                            blu = fromsRGB8LUT16[blu] & 65535;
                            factor = 1.0 / 65535.0;
                        } else {
                            factor = 1.0 / 255.0;
                        }
                        if (supportsAlpha) {
                            alp = (rgb >> 24) & 255;
                            ddata[3] = alp * (1.0 / 255.0);
                            if (isAlphaPremultiplied) {
                                factor *= ddata[3];
                            }
                        }
                        ddata[0] = red * factor;
                        ddata[1] = grn * factor;
                        ddata[2] = blu * factor;
                    } else if (is_LinearGray_stdScale) {
                        red = fromsRGB8LUT16[red] & 65535;
                        grn = fromsRGB8LUT16[grn] & 65535;
                        blu = fromsRGB8LUT16[blu] & 65535;
                        ddata[0] = ((0.2125 * red) + (0.7154 * grn) + (0.0721 * blu)) / 65535.0;
                        if (supportsAlpha) {
                            alp = (rgb >> 24) & 255;
                            ddata[1] = alp * (1.0 / 255.0);
                            if (isAlphaPremultiplied) {
                                ddata[0] *= ddata[1];
                            }
                        }
                    } else if (is_ICCGray_stdScale) {
                        red = fromsRGB8LUT16[red] & 65535;
                        grn = fromsRGB8LUT16[grn] & 65535;
                        blu = fromsRGB8LUT16[blu] & 65535;
                        int gray = (int)((0.2125F * red) + (0.7154F * grn) + (0.0721F * blu) + 0.5F);
                        ddata[0] = (fromLinearGray16ToOtherGray16LUT[gray] & 65535) / 65535.0;
                        if (supportsAlpha) {
                            alp = (rgb >> 24) & 255;
                            ddata[1] = alp * (1.0 / 255.0);
                            if (isAlphaPremultiplied) {
                                ddata[0] *= ddata[1];
                            }
                        }
                    } else {
                        float factor = 1.0F / 255.0F;
                        float[] norm = new float[3];
                        norm[0] = red * factor;
                        norm[1] = grn * factor;
                        norm[2] = blu * factor;
                        norm = colorSpace.fromRGB(norm);
                        if (supportsAlpha) {
                            alp = (rgb >> 24) & 255;
                            ddata[numColorComponents] = alp * (1.0 / 255.0);
                            if (isAlphaPremultiplied) {
                                factor *= alp;
                                for (int i = 0; i < numColorComponents; i++) {
                                    norm[i] *= factor;
                                }
                            }
                        }
                        for (int i = 0; i < numColorComponents; i++) {
                            ddata[i] = norm[i];
                        }
                    }
                    return ddata;
                }
            
            }
        }
        int[] intpixel;
        if (transferType == DataBuffer.TYPE_INT && pixel != null) {
            intpixel = (int[])(int[])pixel;
        } else {
            intpixel = new int[numComponents];
        }
        if (is_sRGB_stdScale || is_LinearRGB_stdScale) {
            int precision;
            float factor;
            if (is_LinearRGB_stdScale) {
                if (transferType == DataBuffer.TYPE_BYTE) {
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
                if (nBits[3] == 8) {
                    intpixel[3] = alp;
                } else {
                    intpixel[3] = (int)(alp * (1.0F / 255.0F) * ((1 << nBits[3]) - 1) + 0.5F);
                }
                if (isAlphaPremultiplied) {
                    factor *= (alp * (1.0F / 255.0F));
                    precision = -1;
                }
            }
            if (nBits[0] == precision) {
                intpixel[0] = red;
            } else {
                intpixel[0] = (int)(red * factor * ((1 << nBits[0]) - 1) + 0.5F);
            }
            if (nBits[1] == precision) {
                intpixel[1] = (int)(grn);
            } else {
                intpixel[1] = (int)(grn * factor * ((1 << nBits[1]) - 1) + 0.5F);
            }
            if (nBits[2] == precision) {
                intpixel[2] = (int)(blu);
            } else {
                intpixel[2] = (int)(blu * factor * ((1 << nBits[2]) - 1) + 0.5F);
            }
        } else if (is_LinearGray_stdScale) {
            red = fromsRGB8LUT16[red] & 65535;
            grn = fromsRGB8LUT16[grn] & 65535;
            blu = fromsRGB8LUT16[blu] & 65535;
            float gray = ((0.2125F * red) + (0.7154F * grn) + (0.0721F * blu)) / 65535.0F;
            if (supportsAlpha) {
                alp = (rgb >> 24) & 255;
                if (nBits[1] == 8) {
                    intpixel[1] = alp;
                } else {
                    intpixel[1] = (int)(alp * (1.0F / 255.0F) * ((1 << nBits[1]) - 1) + 0.5F);
                }
                if (isAlphaPremultiplied) {
                    gray *= (alp * (1.0F / 255.0F));
                }
            }
            intpixel[0] = (int)(gray * ((1 << nBits[0]) - 1) + 0.5F);
        } else if (is_ICCGray_stdScale) {
            red = fromsRGB8LUT16[red] & 65535;
            grn = fromsRGB8LUT16[grn] & 65535;
            blu = fromsRGB8LUT16[blu] & 65535;
            int gray16 = (int)((0.2125F * red) + (0.7154F * grn) + (0.0721F * blu) + 0.5F);
            float gray = (fromLinearGray16ToOtherGray16LUT[gray16] & 65535) / 65535.0F;
            if (supportsAlpha) {
                alp = (rgb >> 24) & 255;
                if (nBits[1] == 8) {
                    intpixel[1] = alp;
                } else {
                    intpixel[1] = (int)(alp * (1.0F / 255.0F) * ((1 << nBits[1]) - 1) + 0.5F);
                }
                if (isAlphaPremultiplied) {
                    gray *= (alp * (1.0F / 255.0F));
                }
            }
            intpixel[0] = (int)(gray * ((1 << nBits[0]) - 1) + 0.5F);
        } else {
            float[] norm = new float[3];
            float factor = 1.0F / 255.0F;
            norm[0] = red * factor;
            norm[1] = grn * factor;
            norm[2] = blu * factor;
            norm = colorSpace.fromRGB(norm);
            if (nonStdScale) {
                for (int i = 0; i < numColorComponents; i++) {
                    norm[i] = (norm[i] - compOffset[i]) * compScale[i];
                    if (norm[i] < 0.0F) {
                        norm[i] = 0.0F;
                    }
                    if (norm[i] > 1.0F) {
                        norm[i] = 1.0F;
                    }
                }
            }
            if (supportsAlpha) {
                alp = (rgb >> 24) & 255;
                if (nBits[numColorComponents] == 8) {
                    intpixel[numColorComponents] = alp;
                } else {
                    intpixel[numColorComponents] = (int)(alp * factor * ((1 << nBits[numColorComponents]) - 1) + 0.5F);
                }
                if (isAlphaPremultiplied) {
                    factor *= alp;
                    for (int i = 0; i < numColorComponents; i++) {
                        norm[i] *= factor;
                    }
                }
            }
            for (int i = 0; i < numColorComponents; i++) {
                intpixel[i] = (int)(norm[i] * ((1 << nBits[i]) - 1) + 0.5F);
            }
        }
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            {
                byte[] bdata;
                if (pixel == null) {
                    bdata = new byte[numComponents];
                } else {
                    bdata = (byte[])(byte[])pixel;
                }
                for (int i = 0; i < numComponents; i++) {
                    bdata[i] = (byte)(255 & intpixel[i]);
                }
                return bdata;
            }
        
        case DataBuffer.TYPE_USHORT: 
            {
                short[] sdata;
                if (pixel == null) {
                    sdata = new short[numComponents];
                } else {
                    sdata = (short[])(short[])pixel;
                }
                for (int i = 0; i < numComponents; i++) {
                    sdata[i] = (short)(intpixel[i] & 65535);
                }
                return sdata;
            }
        
        case DataBuffer.TYPE_INT: 
            if (maxBits > 23) {
                for (int i = 0; i < numComponents; i++) {
                    if (intpixel[i] > ((1 << nBits[i]) - 1)) {
                        intpixel[i] = (1 << nBits[i]) - 1;
                    }
                }
            }
            return intpixel;
        
        }
        throw new IllegalArgumentException("This method has not been " + "implemented for transferType " + transferType);
    }
    
    public int[] getComponents(int pixel, int[] components, int offset) {
        if (numComponents > 1) {
            throw new IllegalArgumentException("More than one component per pixel");
        }
        if (needScaleInit) {
            initScale();
        }
        if (noUnnorm) {
            throw new IllegalArgumentException("This ColorModel does not support the unnormalized form");
        }
        if (components == null) {
            components = new int[offset + 1];
        }
        components[offset + 0] = (pixel & ((1 << nBits[0]) - 1));
        return components;
    }
    
    public int[] getComponents(Object pixel, int[] components, int offset) {
        int[] intpixel;
        if (needScaleInit) {
            initScale();
        }
        if (noUnnorm) {
            throw new IllegalArgumentException("This ColorModel does not support the unnormalized form");
        }
        if (pixel instanceof int[]) {
            intpixel = (int[])(int[])pixel;
        } else {
            intpixel = DataBuffer.toIntArray(pixel);
            if (intpixel == null) {
                throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
            }
        }
        if (intpixel.length < numComponents) {
            throw new IllegalArgumentException("Length of pixel array < number of components in model");
        }
        if (components == null) {
            components = new int[offset + numComponents];
        } else if ((components.length - offset) < numComponents) {
            throw new IllegalArgumentException("Length of components array < number of components in model");
        }
        System.arraycopy(intpixel, 0, components, offset, numComponents);
        return components;
    }
    
    public int[] getUnnormalizedComponents(float[] normComponents, int normOffset, int[] components, int offset) {
        if (needScaleInit) {
            initScale();
        }
        if (noUnnorm) {
            throw new IllegalArgumentException("This ColorModel does not support the unnormalized form");
        }
        return super.getUnnormalizedComponents(normComponents, normOffset, components, offset);
    }
    
    public float[] getNormalizedComponents(int[] components, int offset, float[] normComponents, int normOffset) {
        if (needScaleInit) {
            initScale();
        }
        if (noUnnorm) {
            throw new IllegalArgumentException("This ColorModel does not support the unnormalized form");
        }
        return super.getNormalizedComponents(components, offset, normComponents, normOffset);
    }
    
    public int getDataElement(int[] components, int offset) {
        if (needScaleInit) {
            initScale();
        }
        if (numComponents == 1) {
            if (noUnnorm) {
                throw new IllegalArgumentException("This ColorModel does not support the unnormalized form");
            }
            return components[offset + 0];
        }
        throw new IllegalArgumentException("This model returns " + numComponents + " elements in the pixel array.");
    }
    
    public Object getDataElements(int[] components, int offset, Object obj) {
        if (needScaleInit) {
            initScale();
        }
        if (noUnnorm) {
            throw new IllegalArgumentException("This ColorModel does not support the unnormalized form");
        }
        if ((components.length - offset) < numComponents) {
            throw new IllegalArgumentException("Component array too small" + " (should be " + numComponents);
        }
        switch (transferType) {
        case DataBuffer.TYPE_INT: 
            {
                int[] pixel;
                if (obj == null) {
                    pixel = new int[numComponents];
                } else {
                    pixel = (int[])(int[])obj;
                }
                System.arraycopy(components, offset, pixel, 0, numComponents);
                return pixel;
            }
        
        case DataBuffer.TYPE_BYTE: 
            {
                byte[] pixel;
                if (obj == null) {
                    pixel = new byte[numComponents];
                } else {
                    pixel = (byte[])(byte[])obj;
                }
                for (int i = 0; i < numComponents; i++) {
                    pixel[i] = (byte)(components[offset + i] & 255);
                }
                return pixel;
            }
        
        case DataBuffer.TYPE_USHORT: 
            {
                short[] pixel;
                if (obj == null) {
                    pixel = new short[numComponents];
                } else {
                    pixel = (short[])(short[])obj;
                }
                for (int i = 0; i < numComponents; i++) {
                    pixel[i] = (short)(components[offset + i] & 65535);
                }
                return pixel;
            }
        
        default: 
            throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
        
        }
    }
    
    public int getDataElement(float[] normComponents, int normOffset) {
        if (numComponents > 1) {
            throw new IllegalArgumentException("More than one component per pixel");
        }
        if (signed) {
            throw new IllegalArgumentException("Component value is signed");
        }
        if (needScaleInit) {
            initScale();
        }
        Object pixel = getDataElements(normComponents, normOffset, null);
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            {
                byte[] bpixel = (byte[])(byte[])pixel;
                return bpixel[0] & 255;
            }
        
        case DataBuffer.TYPE_USHORT: 
            {
                short[] uspixel = (short[])(short[])pixel;
                return uspixel[0] & 65535;
            }
        
        case DataBuffer.TYPE_INT: 
            {
                int[] ipixel = (int[])(int[])pixel;
                return ipixel[0];
            }
        
        default: 
            throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
        
        }
    }
    
    public Object getDataElements(float[] normComponents, int normOffset, Object obj) {
        boolean needAlpha = supportsAlpha && isAlphaPremultiplied;
        float[] stdNormComponents;
        if (needScaleInit) {
            initScale();
        }
        if (nonStdScale) {
            stdNormComponents = new float[numComponents];
            for (int c = 0, nc = normOffset; c < numColorComponents; c++, nc++) {
                stdNormComponents[c] = (normComponents[nc] - compOffset[c]) * compScale[c];
                if (stdNormComponents[c] < 0.0F) {
                    stdNormComponents[c] = 0.0F;
                }
                if (stdNormComponents[c] > 1.0F) {
                    stdNormComponents[c] = 1.0F;
                }
            }
            if (supportsAlpha) {
                stdNormComponents[numColorComponents] = normComponents[numColorComponents + normOffset];
            }
            normOffset = 0;
        } else {
            stdNormComponents = normComponents;
        }
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            byte[] bpixel;
            if (obj == null) {
                bpixel = new byte[numComponents];
            } else {
                bpixel = (byte[])(byte[])obj;
            }
            if (needAlpha) {
                float alpha = stdNormComponents[numColorComponents + normOffset];
                for (int c = 0, nc = normOffset; c < numColorComponents; c++, nc++) {
                    bpixel[c] = (byte)((stdNormComponents[nc] * alpha) * ((float)((1 << nBits[c]) - 1)) + 0.5F);
                }
                bpixel[numColorComponents] = (byte)(alpha * ((float)((1 << nBits[numColorComponents]) - 1)) + 0.5F);
            } else {
                for (int c = 0, nc = normOffset; c < numComponents; c++, nc++) {
                    bpixel[c] = (byte)(stdNormComponents[nc] * ((float)((1 << nBits[c]) - 1)) + 0.5F);
                }
            }
            return bpixel;
        
        case DataBuffer.TYPE_USHORT: 
            short[] uspixel;
            if (obj == null) {
                uspixel = new short[numComponents];
            } else {
                uspixel = (short[])(short[])obj;
            }
            if (needAlpha) {
                float alpha = stdNormComponents[numColorComponents + normOffset];
                for (int c = 0, nc = normOffset; c < numColorComponents; c++, nc++) {
                    uspixel[c] = (short)((stdNormComponents[nc] * alpha) * ((float)((1 << nBits[c]) - 1)) + 0.5F);
                }
                uspixel[numColorComponents] = (short)(alpha * ((float)((1 << nBits[numColorComponents]) - 1)) + 0.5F);
            } else {
                for (int c = 0, nc = normOffset; c < numComponents; c++, nc++) {
                    uspixel[c] = (short)(stdNormComponents[nc] * ((float)((1 << nBits[c]) - 1)) + 0.5F);
                }
            }
            return uspixel;
        
        case DataBuffer.TYPE_INT: 
            int[] ipixel;
            if (obj == null) {
                ipixel = new int[numComponents];
            } else {
                ipixel = (int[])(int[])obj;
            }
            if (needAlpha) {
                float alpha = stdNormComponents[numColorComponents + normOffset];
                for (int c = 0, nc = normOffset; c < numColorComponents; c++, nc++) {
                    ipixel[c] = (int)((stdNormComponents[nc] * alpha) * ((float)((1 << nBits[c]) - 1)) + 0.5F);
                }
                ipixel[numColorComponents] = (int)(alpha * ((float)((1 << nBits[numColorComponents]) - 1)) + 0.5F);
            } else {
                for (int c = 0, nc = normOffset; c < numComponents; c++, nc++) {
                    ipixel[c] = (int)(stdNormComponents[nc] * ((float)((1 << nBits[c]) - 1)) + 0.5F);
                }
            }
            return ipixel;
        
        case DataBuffer.TYPE_SHORT: 
            short[] spixel;
            if (obj == null) {
                spixel = new short[numComponents];
            } else {
                spixel = (short[])(short[])obj;
            }
            if (needAlpha) {
                float alpha = stdNormComponents[numColorComponents + normOffset];
                for (int c = 0, nc = normOffset; c < numColorComponents; c++, nc++) {
                    spixel[c] = (short)(stdNormComponents[nc] * alpha * 32767.0F + 0.5F);
                }
                spixel[numColorComponents] = (short)(alpha * 32767.0F + 0.5F);
            } else {
                for (int c = 0, nc = normOffset; c < numComponents; c++, nc++) {
                    spixel[c] = (short)(stdNormComponents[nc] * 32767.0F + 0.5F);
                }
            }
            return spixel;
        
        case DataBuffer.TYPE_FLOAT: 
            float[] fpixel;
            if (obj == null) {
                fpixel = new float[numComponents];
            } else {
                fpixel = (float[])(float[])obj;
            }
            if (needAlpha) {
                float alpha = normComponents[numColorComponents + normOffset];
                for (int c = 0, nc = normOffset; c < numColorComponents; c++, nc++) {
                    fpixel[c] = normComponents[nc] * alpha;
                }
                fpixel[numColorComponents] = alpha;
            } else {
                for (int c = 0, nc = normOffset; c < numComponents; c++, nc++) {
                    fpixel[c] = normComponents[nc];
                }
            }
            return fpixel;
        
        case DataBuffer.TYPE_DOUBLE: 
            double[] dpixel;
            if (obj == null) {
                dpixel = new double[numComponents];
            } else {
                dpixel = (double[])(double[])obj;
            }
            if (needAlpha) {
                double alpha = (double)(normComponents[numColorComponents + normOffset]);
                for (int c = 0, nc = normOffset; c < numColorComponents; c++, nc++) {
                    dpixel[c] = normComponents[nc] * alpha;
                }
                dpixel[numColorComponents] = alpha;
            } else {
                for (int c = 0, nc = normOffset; c < numComponents; c++, nc++) {
                    dpixel[c] = (double)normComponents[nc];
                }
            }
            return dpixel;
        
        default: 
            throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
        
        }
    }
    
    public float[] getNormalizedComponents(Object pixel, float[] normComponents, int normOffset) {
        if (normComponents == null) {
            normComponents = new float[numComponents + normOffset];
        }
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
            byte[] bpixel = (byte[])(byte[])pixel;
            for (int c = 0, nc = normOffset; c < numComponents; c++, nc++) {
                normComponents[nc] = ((float)(bpixel[c] & 255)) / ((float)((1 << nBits[c]) - 1));
            }
            break;
        
        case DataBuffer.TYPE_USHORT: 
            short[] uspixel = (short[])(short[])pixel;
            for (int c = 0, nc = normOffset; c < numComponents; c++, nc++) {
                normComponents[nc] = ((float)(uspixel[c] & 65535)) / ((float)((1 << nBits[c]) - 1));
            }
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] ipixel = (int[])(int[])pixel;
            for (int c = 0, nc = normOffset; c < numComponents; c++, nc++) {
                normComponents[nc] = ((float)ipixel[c]) / ((float)((1 << nBits[c]) - 1));
            }
            break;
        
        case DataBuffer.TYPE_SHORT: 
            short[] spixel = (short[])(short[])pixel;
            for (int c = 0, nc = normOffset; c < numComponents; c++, nc++) {
                normComponents[nc] = ((float)spixel[c]) / 32767.0F;
            }
            break;
        
        case DataBuffer.TYPE_FLOAT: 
            float[] fpixel = (float[])(float[])pixel;
            for (int c = 0, nc = normOffset; c < numComponents; c++, nc++) {
                normComponents[nc] = fpixel[c];
            }
            break;
        
        case DataBuffer.TYPE_DOUBLE: 
            double[] dpixel = (double[])(double[])pixel;
            for (int c = 0, nc = normOffset; c < numComponents; c++, nc++) {
                normComponents[nc] = (float)dpixel[c];
            }
            break;
        
        default: 
            throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
        
        }
        if (supportsAlpha && isAlphaPremultiplied) {
            float alpha = normComponents[numColorComponents + normOffset];
            if (alpha != 0.0F) {
                float invAlpha = 1.0F / alpha;
                for (int c = normOffset; c < numColorComponents + normOffset; c++) {
                    normComponents[c] *= invAlpha;
                }
            }
        }
        if (min != null) {
            for (int c = 0; c < numColorComponents; c++) {
                normComponents[c + normOffset] = min[c] + diffMinMax[c] * normComponents[c + normOffset];
            }
        }
        return normComponents;
    }
    
    public ColorModel coerceData(WritableRaster raster, boolean isAlphaPremultiplied) {
        if ((supportsAlpha == false) || (this.isAlphaPremultiplied == isAlphaPremultiplied)) {
            return this;
        }
        int w = raster.getWidth();
        int h = raster.getHeight();
        int aIdx = raster.getNumBands() - 1;
        float normAlpha;
        int rminX = raster.getMinX();
        int rY = raster.getMinY();
        int rX;
        if (isAlphaPremultiplied) {
            switch (transferType) {
            case DataBuffer.TYPE_BYTE: 
                {
                    byte[] pixel = null;
                    byte[] zpixel = null;
                    float alphaScale = 1.0F / ((float)((1 << nBits[aIdx]) - 1));
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = (byte[])(byte[])raster.getDataElements(rX, rY, pixel);
                            normAlpha = (pixel[aIdx] & 255) * alphaScale;
                            if (normAlpha != 0.0F) {
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] = (byte)((pixel[c] & 255) * normAlpha + 0.5F);
                                }
                                raster.setDataElements(rX, rY, pixel);
                            } else {
                                if (zpixel == null) {
                                    zpixel = new byte[numComponents];
                                    java.util.Arrays.fill(zpixel, (byte)0);
                                }
                                raster.setDataElements(rX, rY, zpixel);
                            }
                        }
                    }
                }
                break;
            
            case DataBuffer.TYPE_USHORT: 
                {
                    short[] pixel = null;
                    short[] zpixel = null;
                    float alphaScale = 1.0F / ((float)((1 << nBits[aIdx]) - 1));
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = (short[])(short[])raster.getDataElements(rX, rY, pixel);
                            normAlpha = (pixel[aIdx] & 65535) * alphaScale;
                            if (normAlpha != 0.0F) {
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] = (short)((pixel[c] & 65535) * normAlpha + 0.5F);
                                }
                                raster.setDataElements(rX, rY, pixel);
                            } else {
                                if (zpixel == null) {
                                    zpixel = new short[numComponents];
                                    java.util.Arrays.fill(zpixel, (short)0);
                                }
                                raster.setDataElements(rX, rY, zpixel);
                            }
                        }
                    }
                }
                break;
            
            case DataBuffer.TYPE_INT: 
                {
                    int[] pixel = null;
                    int[] zpixel = null;
                    float alphaScale = 1.0F / ((float)((1 << nBits[aIdx]) - 1));
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = (int[])(int[])raster.getDataElements(rX, rY, pixel);
                            normAlpha = pixel[aIdx] * alphaScale;
                            if (normAlpha != 0.0F) {
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] = (int)(pixel[c] * normAlpha + 0.5F);
                                }
                                raster.setDataElements(rX, rY, pixel);
                            } else {
                                if (zpixel == null) {
                                    zpixel = new int[numComponents];
                                    java.util.Arrays.fill(zpixel, 0);
                                }
                                raster.setDataElements(rX, rY, zpixel);
                            }
                        }
                    }
                }
                break;
            
            case DataBuffer.TYPE_SHORT: 
                {
                    short[] pixel = null;
                    short[] zpixel = null;
                    float alphaScale = 1.0F / 32767.0F;
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = (short[])(short[])raster.getDataElements(rX, rY, pixel);
                            normAlpha = pixel[aIdx] * alphaScale;
                            if (normAlpha != 0.0F) {
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] = (short)(pixel[c] * normAlpha + 0.5F);
                                }
                                raster.setDataElements(rX, rY, pixel);
                            } else {
                                if (zpixel == null) {
                                    zpixel = new short[numComponents];
                                    java.util.Arrays.fill(zpixel, (short)0);
                                }
                                raster.setDataElements(rX, rY, zpixel);
                            }
                        }
                    }
                }
                break;
            
            case DataBuffer.TYPE_FLOAT: 
                {
                    float[] pixel = null;
                    float[] zpixel = null;
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = (float[])(float[])raster.getDataElements(rX, rY, pixel);
                            normAlpha = pixel[aIdx];
                            if (normAlpha != 0.0F) {
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] *= normAlpha;
                                }
                                raster.setDataElements(rX, rY, pixel);
                            } else {
                                if (zpixel == null) {
                                    zpixel = new float[numComponents];
                                    java.util.Arrays.fill(zpixel, 0.0F);
                                }
                                raster.setDataElements(rX, rY, zpixel);
                            }
                        }
                    }
                }
                break;
            
            case DataBuffer.TYPE_DOUBLE: 
                {
                    double[] pixel = null;
                    double[] zpixel = null;
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = (double[])(double[])raster.getDataElements(rX, rY, pixel);
                            double dnormAlpha = pixel[aIdx];
                            if (dnormAlpha != 0.0) {
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] *= dnormAlpha;
                                }
                                raster.setDataElements(rX, rY, pixel);
                            } else {
                                if (zpixel == null) {
                                    zpixel = new double[numComponents];
                                    java.util.Arrays.fill(zpixel, 0.0);
                                }
                                raster.setDataElements(rX, rY, zpixel);
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
                    byte[] pixel = null;
                    float alphaScale = 1.0F / ((float)((1 << nBits[aIdx]) - 1));
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = (byte[])(byte[])raster.getDataElements(rX, rY, pixel);
                            normAlpha = (pixel[aIdx] & 255) * alphaScale;
                            if (normAlpha != 0.0F) {
                                float invAlpha = 1.0F / normAlpha;
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] = (byte)((pixel[c] & 255) * invAlpha + 0.5F);
                                }
                                raster.setDataElements(rX, rY, pixel);
                            }
                        }
                    }
                }
                break;
            
            case DataBuffer.TYPE_USHORT: 
                {
                    short[] pixel = null;
                    float alphaScale = 1.0F / ((float)((1 << nBits[aIdx]) - 1));
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = (short[])(short[])raster.getDataElements(rX, rY, pixel);
                            normAlpha = (pixel[aIdx] & 65535) * alphaScale;
                            if (normAlpha != 0.0F) {
                                float invAlpha = 1.0F / normAlpha;
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] = (short)((pixel[c] & 65535) * invAlpha + 0.5F);
                                }
                                raster.setDataElements(rX, rY, pixel);
                            }
                        }
                    }
                }
                break;
            
            case DataBuffer.TYPE_INT: 
                {
                    int[] pixel = null;
                    float alphaScale = 1.0F / ((float)((1 << nBits[aIdx]) - 1));
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = (int[])(int[])raster.getDataElements(rX, rY, pixel);
                            normAlpha = pixel[aIdx] * alphaScale;
                            if (normAlpha != 0.0F) {
                                float invAlpha = 1.0F / normAlpha;
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] = (int)(pixel[c] * invAlpha + 0.5F);
                                }
                                raster.setDataElements(rX, rY, pixel);
                            }
                        }
                    }
                }
                break;
            
            case DataBuffer.TYPE_SHORT: 
                {
                    short[] pixel = null;
                    float alphaScale = 1.0F / 32767.0F;
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = (short[])(short[])raster.getDataElements(rX, rY, pixel);
                            normAlpha = pixel[aIdx] * alphaScale;
                            if (normAlpha != 0.0F) {
                                float invAlpha = 1.0F / normAlpha;
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] = (short)(pixel[c] * invAlpha + 0.5F);
                                }
                                raster.setDataElements(rX, rY, pixel);
                            }
                        }
                    }
                }
                break;
            
            case DataBuffer.TYPE_FLOAT: 
                {
                    float[] pixel = null;
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = (float[])(float[])raster.getDataElements(rX, rY, pixel);
                            normAlpha = pixel[aIdx];
                            if (normAlpha != 0.0F) {
                                float invAlpha = 1.0F / normAlpha;
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] *= invAlpha;
                                }
                                raster.setDataElements(rX, rY, pixel);
                            }
                        }
                    }
                }
                break;
            
            case DataBuffer.TYPE_DOUBLE: 
                {
                    double[] pixel = null;
                    for (int y = 0; y < h; y++, rY++) {
                        rX = rminX;
                        for (int x = 0; x < w; x++, rX++) {
                            pixel = (double[])(double[])raster.getDataElements(rX, rY, pixel);
                            double dnormAlpha = pixel[aIdx];
                            if (dnormAlpha != 0.0) {
                                double invAlpha = 1.0 / dnormAlpha;
                                for (int c = 0; c < aIdx; c++) {
                                    pixel[c] *= invAlpha;
                                }
                                raster.setDataElements(rX, rY, pixel);
                            }
                        }
                    }
                }
                break;
            
            default: 
                throw new UnsupportedOperationException("This method has not been " + "implemented for transferType " + transferType);
            
            }
        }
        if (!signed) {
            return new ComponentColorModel(colorSpace, nBits, supportsAlpha, isAlphaPremultiplied, transparency, transferType);
        } else {
            return new ComponentColorModel(colorSpace, supportsAlpha, isAlphaPremultiplied, transparency, transferType);
        }
    }
    
    public boolean isCompatibleRaster(Raster raster) {
        SampleModel sm = raster.getSampleModel();
        if (sm instanceof ComponentSampleModel) {
            if (sm.getNumBands() != getNumComponents()) {
                return false;
            }
            for (int i = 0; i < nBits.length; i++) {
                if (sm.getSampleSize(i) < nBits[i]) {
                    return false;
                }
            }
            return (raster.getTransferType() == transferType);
        } else {
            return false;
        }
    }
    
    public WritableRaster createCompatibleWritableRaster(int w, int h) {
        int dataSize = w * h * numComponents;
        WritableRaster raster = null;
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
        
        case DataBuffer.TYPE_USHORT: 
            raster = Raster.createInterleavedRaster(transferType, w, h, numComponents, null);
            break;
        
        default: 
            SampleModel sm = createCompatibleSampleModel(w, h);
            DataBuffer db = sm.createDataBuffer();
            raster = Raster.createWritableRaster(sm, db, null);
        
        }
        return raster;
    }
    
    public SampleModel createCompatibleSampleModel(int w, int h) {
        int[] bandOffsets = new int[numComponents];
        for (int i = 0; i < numComponents; i++) {
            bandOffsets[i] = i;
        }
        switch (transferType) {
        case DataBuffer.TYPE_BYTE: 
        
        case DataBuffer.TYPE_USHORT: 
            return new PixelInterleavedSampleModel(transferType, w, h, numComponents, w * numComponents, bandOffsets);
        
        default: 
            return new ComponentSampleModel(transferType, w, h, numComponents, w * numComponents, bandOffsets);
        
        }
    }
    
    public boolean isCompatibleSampleModel(SampleModel sm) {
        if (!(sm instanceof ComponentSampleModel)) {
            return false;
        }
        if (numComponents != sm.getNumBands()) {
            return false;
        }
        if (sm.getTransferType() != transferType) {
            return false;
        }
        return true;
    }
    
    public WritableRaster getAlphaRaster(WritableRaster raster) {
        if (hasAlpha() == false) {
            return null;
        }
        int x = raster.getMinX();
        int y = raster.getMinY();
        int[] band = new int[1];
        band[0] = raster.getNumBands() - 1;
        return raster.createWritableChild(x, y, raster.getWidth(), raster.getHeight(), x, y, band);
    }
    
    public boolean equals(Object obj) {
        if (!super.equals(obj)) {
            return false;
        }
        if (obj.getClass() != getClass()) {
            return false;
        }
        return true;
    }
}
