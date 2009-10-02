package java.awt.image;

import java.awt.geom.Rectangle2D;
import java.awt.RenderingHints;
import java.awt.geom.Point2D;
import sun.awt.image.ImagingLib;

public class LookupOp implements BufferedImageOp, RasterOp {
    private LookupTable ltable;
    private int numComponents;
    RenderingHints hints;
    
    public LookupOp(LookupTable lookup, RenderingHints hints) {
        
        this.ltable = lookup;
        this.hints = hints;
        numComponents = ltable.getNumComponents();
    }
    
    public final LookupTable getTable() {
        return ltable;
    }
    
    public final BufferedImage filter(BufferedImage src, BufferedImage dst) {
        ColorModel srcCM = src.getColorModel();
        int numBands = srcCM.getNumColorComponents();
        ColorModel dstCM;
        if (srcCM instanceof IndexColorModel) {
            throw new IllegalArgumentException("LookupOp cannot be performed on an indexed image");
        }
        int numComponents = ltable.getNumComponents();
        if (numComponents != 1 && numComponents != srcCM.getNumComponents() && numComponents != srcCM.getNumColorComponents()) {
            throw new IllegalArgumentException("Number of arrays in the " + " lookup table (" + numComponents + " is not compatible with the " + " src image: " + src);
        }
        boolean needToConvert = false;
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
                if (numBands - 1 == numComponents || numComponents == 1) {
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
                if (dstNumBands - 1 == numComponents || numComponents == 1) {
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
        int dstLength = dst.getNumBands();
        int height = src.getHeight();
        int width = src.getWidth();
        int[] srcPix = new int[numBands];
        if (dst == null) {
            dst = createCompatibleDestRaster(src);
        } else if (height != dst.getHeight() || width != dst.getWidth()) {
            throw new IllegalArgumentException("Width or height of Rasters do not match");
        }
        dstLength = dst.getNumBands();
        if (numBands != dstLength) {
            throw new IllegalArgumentException("Number of channels in the src (" + numBands + ") does not match number of channels" + " in the destination (" + dstLength + ")");
        }
        int numComponents = ltable.getNumComponents();
        if (numComponents != 1 && numComponents != src.getNumBands()) {
            throw new IllegalArgumentException("Number of arrays in the " + " lookup table (" + numComponents + " is not compatible with the " + " src Raster: " + src);
        }
        if (ImagingLib.filter(this, src, dst) != null) {
            return dst;
        }
        if (ltable instanceof ByteLookupTable) {
            byteFilter((ByteLookupTable)(ByteLookupTable)ltable, src, dst, width, height, numBands);
        } else if (ltable instanceof ShortLookupTable) {
            shortFilter((ShortLookupTable)(ShortLookupTable)ltable, src, dst, width, height, numBands);
        } else {
            int sminX = src.getMinX();
            int sY = src.getMinY();
            int dminX = dst.getMinX();
            int dY = dst.getMinY();
            for (int y = 0; y < height; y++, sY++, dY++) {
                int sX = sminX;
                int dX = dminX;
                for (int x = 0; x < width; x++, sX++, dX++) {
                    src.getPixel(sX, sY, srcPix);
                    ltable.lookupPixel(srcPix, srcPix);
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
        int w = src.getWidth();
        int h = src.getHeight();
        int transferType = DataBuffer.TYPE_BYTE;
        if (destCM == null) {
            ColorModel cm = src.getColorModel();
            Raster raster = src.getRaster();
            if (cm instanceof ComponentColorModel) {
                DataBuffer db = raster.getDataBuffer();
                boolean hasAlpha = cm.hasAlpha();
                boolean isPre = cm.isAlphaPremultiplied();
                int trans = cm.getTransparency();
                int[] nbits = null;
                if (ltable instanceof ByteLookupTable) {
                    if (db.getDataType() == db.TYPE_USHORT) {
                        if (hasAlpha) {
                            nbits = new int[2];
                            if (trans == cm.BITMASK) {
                                nbits[1] = 1;
                            } else {
                                nbits[1] = 8;
                            }
                        } else {
                            nbits = new int[1];
                        }
                        nbits[0] = 8;
                    }
                } else if (ltable instanceof ShortLookupTable) {
                    transferType = DataBuffer.TYPE_USHORT;
                    if (db.getDataType() == db.TYPE_BYTE) {
                        if (hasAlpha) {
                            nbits = new int[2];
                            if (trans == cm.BITMASK) {
                                nbits[1] = 1;
                            } else {
                                nbits[1] = 16;
                            }
                        } else {
                            nbits = new int[1];
                        }
                        nbits[0] = 16;
                    }
                }
                if (nbits != null) {
                    cm = new ComponentColorModel(cm.getColorSpace(), nbits, hasAlpha, isPre, trans, transferType);
                }
            }
            image = new BufferedImage(cm, cm.createCompatibleWritableRaster(w, h), cm.isAlphaPremultiplied(), null);
        } else {
            image = new BufferedImage(destCM, destCM.createCompatibleWritableRaster(w, h), destCM.isAlphaPremultiplied(), null);
        }
        return image;
    }
    
    public WritableRaster createCompatibleDestRaster(Raster src) {
        return src.createCompatibleWritableRaster();
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
    
    private final void byteFilter(ByteLookupTable lookup, Raster src, WritableRaster dst, int width, int height, int numBands) {
        int[] srcPix = null;
        byte[][] table = lookup.getTable();
        int offset = lookup.getOffset();
        int tidx;
        int step = 1;
        if (table.length == 1) {
            step = 0;
        }
        int x;
        int y;
        int band;
        int len = table[0].length;
        for (y = 0; y < height; y++) {
            tidx = 0;
            for (band = 0; band < numBands; band++, tidx += step) {
                srcPix = src.getSamples(0, y, width, 1, band, srcPix);
                for (x = 0; x < width; x++) {
                    int index = srcPix[x] - offset;
                    if (index < 0 || index > len) {
                        throw new IllegalArgumentException("index (" + index + "(out of range: " + " srcPix[" + x + "]=" + srcPix[x] + " offset=" + offset);
                    }
                    srcPix[x] = table[tidx][index];
                }
                dst.setSamples(0, y, width, 1, band, srcPix);
            }
        }
    }
    
    private final void shortFilter(ShortLookupTable lookup, Raster src, WritableRaster dst, int width, int height, int numBands) {
        int band;
        int[] srcPix = null;
        short[][] table = lookup.getTable();
        int offset = lookup.getOffset();
        int tidx;
        int step = 1;
        if (table.length == 1) {
            step = 0;
        }
        int x = 0;
        int y = 0;
        int index;
        int maxShort = (1 << 16) - 1;
        for (y = 0; y < height; y++) {
            tidx = 0;
            for (band = 0; band < numBands; band++, tidx += step) {
                srcPix = src.getSamples(0, y, width, 1, band, srcPix);
                for (x = 0; x < width; x++) {
                    index = srcPix[x] - offset;
                    if (index < 0 || index > maxShort) {
                        throw new IllegalArgumentException("index out of range " + index + " x is " + x + "srcPix[x]=" + srcPix[x] + " offset=" + offset);
                    }
                    srcPix[x] = table[tidx][index];
                }
                dst.setSamples(0, y, width, 1, band, srcPix);
            }
        }
    }
}
