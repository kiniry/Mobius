package java.awt.image;

import java.awt.geom.Rectangle2D;
import java.awt.RenderingHints;
import java.awt.geom.Point2D;
import sun.awt.image.ImagingLib;

public class ConvolveOp implements BufferedImageOp, RasterOp {
    Kernel kernel;
    int edgeHint;
    RenderingHints hints;
    public static final int EDGE_ZERO_FILL = 0;
    public static final int EDGE_NO_OP = 1;
    
    public ConvolveOp(Kernel kernel, int edgeCondition, RenderingHints hints) {
        
        this.kernel = kernel;
        this.edgeHint = edgeCondition;
        this.hints = hints;
    }
    
    public ConvolveOp(Kernel kernel) {
        
        this.kernel = kernel;
        this.edgeHint = EDGE_ZERO_FILL;
    }
    
    public int getEdgeCondition() {
        return edgeHint;
    }
    
    public final Kernel getKernel() {
        return (Kernel)(Kernel)kernel.clone();
    }
    
    public final BufferedImage filter(BufferedImage src, BufferedImage dst) {
        if (src == null) {
            throw new NullPointerException("src image is null");
        }
        if (src == dst) {
            throw new IllegalArgumentException("src image cannot be the same as the dst image");
        }
        boolean needToConvert = false;
        ColorModel srcCM = src.getColorModel();
        ColorModel dstCM;
        BufferedImage origDst = dst;
        if (srcCM instanceof IndexColorModel) {
            IndexColorModel icm = (IndexColorModel)(IndexColorModel)srcCM;
            src = icm.convertToIntDiscrete(src.getRaster(), false);
            srcCM = src.getColorModel();
        }
        if (dst == null) {
            dst = createCompatibleDestImage(src, null);
            dstCM = srcCM;
            origDst = dst;
        } else {
            dstCM = dst.getColorModel();
            if (srcCM.getColorSpace().getType() != dstCM.getColorSpace().getType()) {
                needToConvert = true;
                dst = createCompatibleDestImage(src, null);
                dstCM = dst.getColorModel();
            } else if (dstCM instanceof IndexColorModel) {
                dst = createCompatibleDestImage(src, null);
                dstCM = dst.getColorModel();
            }
        }
        if (ImagingLib.filter(this, src, dst) == null) {
            throw new ImagingOpException("Unable to convolve src image");
        }
        if (needToConvert) {
            ColorConvertOp ccop = new ColorConvertOp(hints);
            ccop.filter(dst, origDst);
        } else if (origDst != dst) {
            java.awt.Graphics2D g = origDst.createGraphics();
            try {
                g.drawImage(dst, 0, 0, null);
            } finally {
                g.dispose();
            }
        }
        return origDst;
    }
    
    public final WritableRaster filter(Raster src, WritableRaster dst) {
        if (dst == null) {
            dst = createCompatibleDestRaster(src);
        } else if (src == dst) {
            throw new IllegalArgumentException("src image cannot be the same as the dst image");
        } else if (src.getNumBands() != dst.getNumBands()) {
            throw new ImagingOpException("Different number of bands in src  and dst Rasters");
        }
        if (ImagingLib.filter(this, src, dst) == null) {
            throw new ImagingOpException("Unable to convolve src image");
        }
        return dst;
    }
    
    public BufferedImage createCompatibleDestImage(BufferedImage src, ColorModel destCM) {
        BufferedImage image;
        if (destCM == null) {
            destCM = src.getColorModel();
            if (destCM instanceof IndexColorModel) {
                destCM = ColorModel.getRGBdefault();
            }
        }
        int w = src.getWidth();
        int h = src.getHeight();
        image = new BufferedImage(destCM, destCM.createCompatibleWritableRaster(w, h), destCM.isAlphaPremultiplied(), null);
        return image;
    }
    
    public WritableRaster createCompatibleDestRaster(Raster src) {
        return src.createCompatibleWritableRaster();
    }
    
    public final Rectangle2D getBounds2D(BufferedImage src) {
        return getBounds2D(src.getRaster());
    }
    
    public final Rectangle2D getBounds2D(Raster src) {
        return src.getBounds();
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
