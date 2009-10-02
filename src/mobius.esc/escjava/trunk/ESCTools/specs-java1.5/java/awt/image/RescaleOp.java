package java.awt.image;

import java.awt.geom.Rectangle2D;
import java.awt.geom.Point2D;
import java.awt.RenderingHints;
import sun.awt.image.ImagingLib;

public class RescaleOp implements BufferedImageOp, RasterOp {
    float[] scaleFactors;
    float[] offsets;
    int length = 0;
    RenderingHints hints;
    private int srcNbits;
    private int dstNbits;
    
    public RescaleOp(float[] scaleFactors, float[] offsets, RenderingHints hints) {
        
        length = scaleFactors.length;
        if (length > offsets.length) length = offsets.length;
        this.scaleFactors = new float[length];
        this.offsets = new float[length];
        for (int i = 0; i < length; i++) {
            this.scaleFactors[i] = scaleFactors[i];
            this.offsets[i] = offsets[i];
        }
        this.hints = hints;
    }
    
    public RescaleOp(float scaleFactor, float offset, RenderingHints hints) {
        
        length = 1;
        this.scaleFactors = new float[1];
        this.offsets = new float[1];
        this.scaleFactors[0] = scaleFactor;
        this.offsets[0] = offset;
        this.hints = hints;
    }
    
    public final float[] getScaleFactors(float[] scaleFactors) {
        if (scaleFactors == null) {
            return (float[])(float[])this.scaleFactors.clone();
        }
        System.arraycopy(this.scaleFactors, 0, scaleFactors, 0, Math.min(this.scaleFactors.length, scaleFactors.length));
        return scaleFactors;
    }
    
    public final float[] getOffsets(float[] offsets) {
        if (offsets == null) {
            return (float[])(float[])this.offsets.clone();
        }
        System.arraycopy(this.offsets, 0, offsets, 0, Math.min(this.offsets.length, offsets.length));
        return offsets;
    }
    
    public final int getNumFactors() {
        return length;
    }
    
    private ByteLookupTable createByteLut(float[] scale, float[] off, int nBands, int nElems) {
        byte[][] lutData = new byte[scale.length][nElems];
        for (int band = 0; band < scale.length; band++) {
            float bandScale = scale[band];
            float bandOff = off[band];
            byte[] bandLutData = lutData[band];
            for (int i = 0; i < nElems; i++) {
                int val = (int)(i * bandScale + bandOff);
                if ((val & -256) != 0) {
                    if (val < 0) {
                        val = 0;
                    } else {
                        val = 255;
                    }
                }
                bandLutData[i] = (byte)val;
            }
        }
        return new ByteLookupTable(0, lutData);
    }
    
    private ShortLookupTable createShortLut(float[] scale, float[] off, int nBands, int nElems) {
        short[][] lutData = new short[scale.length][nElems];
        for (int band = 0; band < scale.length; band++) {
            float bandScale = scale[band];
            float bandOff = off[band];
            short[] bandLutData = lutData[band];
            for (int i = 0; i < nElems; i++) {
                int val = (int)(i * bandScale + bandOff);
                if ((val & -65536) != 0) {
                    if (val < 0) {
                        val = 0;
                    } else {
                        val = 65535;
                    }
                }
                bandLutData[i] = (short)val;
            }
        }
        return new ShortLookupTable(0, lutData);
    }
    
    private boolean canUseLookup(Raster src, Raster dst) {
        int datatype = src.getDataBuffer().getDataType();
        if (datatype != DataBuffer.TYPE_BYTE && datatype != DataBuffer.TYPE_USHORT) {
            return false;
        }
        SampleModel dstSM = dst.getSampleModel();
        dstNbits = dstSM.getSampleSize(0);
        if (!(dstNbits == 8 || dstNbits == 16)) {
            return false;
        }
        for (int i = 1; i < src.getNumBands(); i++) {
            int bandSize = dstSM.getSampleSize(i);
            if (bandSize != dstNbits) {
                return false;
            }
        }
        SampleModel srcSM = src.getSampleModel();
        srcNbits = srcSM.getSampleSize(0);
        if (srcNbits > 16) {
            return false;
        }
        for (int i = 1; i < src.getNumBands(); i++) {
            int bandSize = srcSM.getSampleSize(i);
            if (bandSize != srcNbits) {
                return false;
            }
        }
        return true;
    }
    
    public final BufferedImage filter(BufferedImage src, BufferedImage dst) {
        ColorModel srcCM = src.getColorModel();
        ColorModel dstCM;
        int numBands = srcCM.getNumColorComponents();
        if (srcCM instanceof IndexColorModel) {
            throw new IllegalArgumentException("Rescaling cannot be performed on an indexed image");
        }
        if (length != 1 && length != numBands && length != srcCM.getNumComponents()) {
            throw new IllegalArgumentException("Number of scaling constants does not equal the number of of color or color/alpha  components");
        }
        boolean needToConvert = false;
        if (length > numBands && srcCM.hasAlpha()) {
            length = numBands + 1;
        }
        int width = src.getWidth();
        int height = src.getHeight();
        if (dst == null) {
            dst = createCompatibleDestImage(src, null);
            dstCM = srcCM;
        } else {
            if (width != dst.getWidth()) {
                throw new IllegalArgumentException("Src width (" + width + ") not equal to dst width (" + dst.getWidth() + ")");
            }
            if (height != dst.getHeight()) {
                throw new IllegalArgumentException("Src height (" + height + ") not equal to dst height (" + dst.getHeight() + ")");
            }
            dstCM = dst.getColorModel();
            if (srcCM.getColorSpace().getType() != dstCM.getColorSpace().getType()) {
                needToConvert = true;
                dst = createCompatibleDestImage(src, null);
            }
        }
        BufferedImage origDst = dst;
        if (ImagingLib.filter(this, src, dst) == null) {
            WritableRaster srcRaster = src.getRaster();
            WritableRaster dstRaster = dst.getRaster();
            if (srcCM.hasAlpha()) {
                if (numBands - 1 == length || length == 1) {
                    int minx = srcRaster.getMinX();
                    int miny = srcRaster.getMinY();
                    int[] bands = new int[numBands - 1];
                    for (int i = 0; i < numBands - 1; i++) {
                        bands[i] = i;
                    }
                    srcRaster = srcRaster.createWritableChild(minx, miny, srcRaster.getWidth(), srcRaster.getHeight(), minx, miny, bands);
                }
            }
            if (dstCM.hasAlpha()) {
                int dstNumBands = dstRaster.getNumBands();
                if (dstNumBands - 1 == length || length == 1) {
                    int minx = dstRaster.getMinX();
                    int miny = dstRaster.getMinY();
                    int[] bands = new int[numBands - 1];
                    for (int i = 0; i < numBands - 1; i++) {
                        bands[i] = i;
                    }
                    dstRaster = dstRaster.createWritableChild(minx, miny, dstRaster.getWidth(), dstRaster.getHeight(), minx, miny, bands);
                }
            }
            filter(srcRaster, dstRaster);
        }
        if (needToConvert) {
            ColorConvertOp ccop = new ColorConvertOp(hints);
            ccop.filter(dst, origDst);
        }
        return origDst;
    }
    
    public final WritableRaster filter(Raster src, WritableRaster dst) {
        int numBands = src.getNumBands();
        int width = src.getWidth();
        int height = src.getHeight();
        int[] srcPix = null;
        int step = 0;
        int tidx = 0;
        if (dst == null) {
            dst = createCompatibleDestRaster(src);
        } else if (height != dst.getHeight() || width != dst.getWidth()) {
            throw new IllegalArgumentException("Width or height of Rasters do not match");
        } else if (numBands != dst.getNumBands()) {
            throw new IllegalArgumentException("Number of bands in src " + numBands + " does not equal number of bands in dest " + dst.getNumBands());
        }
        if (length != 1 && length != src.getNumBands()) {
            throw new IllegalArgumentException("Number of scaling constants does not equal the number of of bands in the src raster");
        }
        if (ImagingLib.filter(this, src, dst) != null) {
            return dst;
        }
        if (canUseLookup(src, dst)) {
            int srcNgray = (1 << srcNbits);
            int dstNgray = (1 << dstNbits);
            if (dstNgray == 256) {
                ByteLookupTable lut = createByteLut(scaleFactors, offsets, numBands, srcNgray);
                LookupOp op = new LookupOp(lut, hints);
                op.filter(src, dst);
            } else {
                ShortLookupTable lut = createShortLut(scaleFactors, offsets, numBands, srcNgray);
                LookupOp op = new LookupOp(lut, hints);
                op.filter(src, dst);
            }
        } else {
            if (length > 1) {
                step = 1;
            }
            int sminX = src.getMinX();
            int sY = src.getMinY();
            int dminX = dst.getMinX();
            int dY = dst.getMinY();
            int sX;
            int dX;
            int nbits;
            int[] dstMax = new int[numBands];
            int[] dstMask = new int[numBands];
            SampleModel dstSM = dst.getSampleModel();
            for (int z = 0; z < numBands; z++) {
                nbits = dstSM.getSampleSize(z);
                dstMax[z] = (1 << nbits) - 1;
                dstMask[z] = ~(dstMax[z]);
            }
            int val;
            for (int y = 0; y < height; y++, sY++, dY++) {
                dX = dminX;
                sX = sminX;
                for (int x = 0; x < width; x++, sX++, dX++) {
                    srcPix = src.getPixel(sX, sY, srcPix);
                    tidx = 0;
                    for (int z = 0; z < numBands; z++, tidx += step) {
                        val = (int)(srcPix[z] * scaleFactors[tidx] + offsets[tidx]);
                        if ((val & dstMask[z]) != 0) {
                            if (val < 0) {
                                val = 0;
                            } else {
                                val = dstMax[z];
                            }
                        }
                        srcPix[z] = val;
                    }
                    dst.setPixel(dX, dY, srcPix);
                }
            }
        }
        return dst;
    }
    
    public final Rectangle2D getBounds2D(BufferedImage src) {
        return getBounds2D(src.getRaster());
    }
    
    public final Rectangle2D getBounds2D(Raster src) {
        return src.getBounds();
    }
    
    public BufferedImage createCompatibleDestImage(BufferedImage src, ColorModel destCM) {
        BufferedImage image;
        if (destCM == null) {
            ColorModel cm = src.getColorModel();
            image = new BufferedImage(cm, src.getRaster().createCompatibleWritableRaster(), cm.isAlphaPremultiplied(), null);
        } else {
            int w = src.getWidth();
            int h = src.getHeight();
            image = new BufferedImage(destCM, destCM.createCompatibleWritableRaster(w, h), destCM.isAlphaPremultiplied(), null);
        }
        return image;
    }
    
    public WritableRaster createCompatibleDestRaster(Raster src) {
        return src.createCompatibleWritableRaster(src.getWidth(), src.getHeight());
    }
    
    public final Point2D getPoint2D(Point2D srcPt, Point2D dstPt) {
        if (dstPt == null) {
            dstPt = new Point2D$Float();
        }
        dstPt.setLocation(srcPt.getX(), srcPt.getY());
        return dstPt;
    }
    
    public final RenderingHints getRenderingHints() {
        return hints;
    }
}
