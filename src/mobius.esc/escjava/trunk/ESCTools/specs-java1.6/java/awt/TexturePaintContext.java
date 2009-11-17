package java.awt;

import java.awt.image.BufferedImage;
import java.awt.image.Raster;
import java.awt.image.WritableRaster;
import java.awt.image.ColorModel;
import java.awt.image.DirectColorModel;
import java.awt.image.IndexColorModel;
import java.awt.geom.AffineTransform;
import java.awt.geom.NoninvertibleTransformException;
import java.lang.ref.WeakReference;
import sun.awt.image.IntegerInterleavedRaster;
import sun.awt.image.ByteInterleavedRaster;

abstract class TexturePaintContext implements PaintContext {
    public static ColorModel xrgbmodel = new DirectColorModel(24, 16711680, 65280, 255);
    public static ColorModel argbmodel = ColorModel.getRGBdefault();
    ColorModel colorModel;
    int bWidth;
    int bHeight;
    int maxWidth;
    WritableRaster outRas;
    double xOrg;
    double yOrg;
    double incXAcross;
    double incYAcross;
    double incXDown;
    double incYDown;
    int colincx;
    int colincy;
    int colincxerr;
    int colincyerr;
    int rowincx;
    int rowincy;
    int rowincxerr;
    int rowincyerr;
    
    public static PaintContext getContext(BufferedImage bufImg, AffineTransform xform, RenderingHints hints, Rectangle devBounds) {
        WritableRaster raster = bufImg.getRaster();
        ColorModel cm = bufImg.getColorModel();
        int maxw = devBounds.width;
        Object val = hints.get(hints.KEY_INTERPOLATION);
        boolean filter = (val == null ? (hints.get(hints.KEY_RENDERING) == hints.VALUE_RENDER_QUALITY) : (val != hints.VALUE_INTERPOLATION_NEAREST_NEIGHBOR));
        if (raster instanceof IntegerInterleavedRaster && (!filter || isFilterableDCM(cm))) {
            IntegerInterleavedRaster iir = (IntegerInterleavedRaster)(IntegerInterleavedRaster)raster;
            if (iir.getNumDataElements() == 1 && iir.getPixelStride() == 1) {
                return new TexturePaintContext$Int(iir, cm, xform, maxw, filter);
            }
        } else if (raster instanceof ByteInterleavedRaster) {
            ByteInterleavedRaster bir = (ByteInterleavedRaster)(ByteInterleavedRaster)raster;
            if (bir.getNumDataElements() == 1 && bir.getPixelStride() == 1) {
                if (filter) {
                    if (isFilterableICM(cm)) {
                        return new TexturePaintContext$ByteFilter(bir, cm, xform, maxw);
                    }
                } else {
                    return new TexturePaintContext$Byte(bir, cm, xform, maxw);
                }
            }
        }
        return new TexturePaintContext$Any(raster, cm, xform, maxw, filter);
    }
    
    public static boolean isFilterableICM(ColorModel cm) {
        if (cm instanceof IndexColorModel) {
            IndexColorModel icm = (IndexColorModel)(IndexColorModel)cm;
            if (icm.getMapSize() <= 256) {
                return true;
            }
        }
        return false;
    }
    
    public static boolean isFilterableDCM(ColorModel cm) {
        if (cm instanceof DirectColorModel) {
            DirectColorModel dcm = (DirectColorModel)(DirectColorModel)cm;
            return (isMaskOK(dcm.getAlphaMask(), true) && isMaskOK(dcm.getRedMask(), false) && isMaskOK(dcm.getGreenMask(), false) && isMaskOK(dcm.getBlueMask(), false));
        }
        return false;
    }
    
    public static boolean isMaskOK(int mask, boolean canbezero) {
        if (canbezero && mask == 0) {
            return true;
        }
        return (mask == 255 || mask == 65280 || mask == 16711680 || mask == -16777216);
    }
    
    public static ColorModel getInternedColorModel(ColorModel cm) {
        if (xrgbmodel == cm || xrgbmodel.equals(cm)) {
            return xrgbmodel;
        }
        if (argbmodel == cm || argbmodel.equals(cm)) {
            return argbmodel;
        }
        return cm;
    }
    
    TexturePaintContext(ColorModel cm, AffineTransform xform, int bWidth, int bHeight, int maxw) {
        
        this.colorModel = getInternedColorModel(cm);
        this.bWidth = bWidth;
        this.bHeight = bHeight;
        this.maxWidth = maxw;
        try {
            xform = xform.createInverse();
        } catch (NoninvertibleTransformException e) {
            xform.setToScale(0, 0);
        }
        this.incXAcross = mod(xform.getScaleX(), bWidth);
        this.incYAcross = mod(xform.getShearY(), bHeight);
        this.incXDown = mod(xform.getShearX(), bWidth);
        this.incYDown = mod(xform.getScaleY(), bHeight);
        this.xOrg = xform.getTranslateX();
        this.yOrg = xform.getTranslateY();
        this.colincx = (int)incXAcross;
        this.colincy = (int)incYAcross;
        this.colincxerr = fractAsInt(incXAcross);
        this.colincyerr = fractAsInt(incYAcross);
        this.rowincx = (int)incXDown;
        this.rowincy = (int)incYDown;
        this.rowincxerr = fractAsInt(incXDown);
        this.rowincyerr = fractAsInt(incYDown);
    }
    
    static int fractAsInt(double d) {
        return (int)((d % 1.0) * Integer.MAX_VALUE);
    }
    
    static double mod(double num, double den) {
        num = num % den;
        if (num < 0) {
            num += den;
            if (num >= den) {
                num = 0;
            }
        }
        return num;
    }
    
    public void dispose() {
        dropRaster(colorModel, outRas);
    }
    
    public ColorModel getColorModel() {
        return colorModel;
    }
    
    public Raster getRaster(int x, int y, int w, int h) {
        if (outRas == null || outRas.getWidth() < w || outRas.getHeight() < h) {
            outRas = makeRaster((h == 1 ? Math.max(w, maxWidth) : w), h);
        }
        double X = mod(xOrg + x * incXAcross + y * incXDown, bWidth);
        double Y = mod(yOrg + x * incYAcross + y * incYDown, bHeight);
        setRaster((int)X, (int)Y, fractAsInt(X), fractAsInt(Y), w, h, bWidth, bHeight, colincx, colincxerr, colincy, colincyerr, rowincx, rowincxerr, rowincy, rowincyerr);
        return outRas;
    }
    private static WeakReference xrgbRasRef;
    private static WeakReference argbRasRef;
    
    static synchronized WritableRaster makeRaster(ColorModel cm, Raster srcRas, int w, int h) {
        if (xrgbmodel == cm) {
            if (xrgbRasRef != null) {
                WritableRaster wr = (WritableRaster)(WritableRaster)xrgbRasRef.get();
                if (wr != null && wr.getWidth() >= w && wr.getHeight() >= h) {
                    xrgbRasRef = null;
                    return wr;
                }
            }
            if (w <= 32 && h <= 32) {
                w = h = 32;
            }
        } else if (argbmodel == cm) {
            if (argbRasRef != null) {
                WritableRaster wr = (WritableRaster)(WritableRaster)argbRasRef.get();
                if (wr != null && wr.getWidth() >= w && wr.getHeight() >= h) {
                    argbRasRef = null;
                    return wr;
                }
            }
            if (w <= 32 && h <= 32) {
                w = h = 32;
            }
        }
        if (srcRas != null) {
            return srcRas.createCompatibleWritableRaster(w, h);
        } else {
            return cm.createCompatibleWritableRaster(w, h);
        }
    }
    
    static synchronized void dropRaster(ColorModel cm, Raster outRas) {
        if (outRas == null) {
            return;
        }
        if (xrgbmodel == cm) {
            xrgbRasRef = new WeakReference(outRas);
        } else if (argbmodel == cm) {
            argbRasRef = new WeakReference(outRas);
        }
    }
    private static WeakReference byteRasRef;
    
    static synchronized WritableRaster makeByteRaster(Raster srcRas, int w, int h) {
        if (byteRasRef != null) {
            WritableRaster wr = (WritableRaster)(WritableRaster)byteRasRef.get();
            if (wr != null && wr.getWidth() >= w && wr.getHeight() >= h) {
                byteRasRef = null;
                return wr;
            }
        }
        if (w <= 32 && h <= 32) {
            w = h = 32;
        }
        return srcRas.createCompatibleWritableRaster(w, h);
    }
    
    static synchronized void dropByteRaster(Raster outRas) {
        if (outRas == null) {
            return;
        }
        byteRasRef = new WeakReference(outRas);
    }
    
    public abstract WritableRaster makeRaster(int w, int h);
    
    public abstract void setRaster(int x, int y, int xerr, int yerr, int w, int h, int bWidth, int bHeight, int colincx, int colincxerr, int colincy, int colincyerr, int rowincx, int rowincxerr, int rowincy, int rowincyerr);
    
    public static int blend(int[] rgbs, int xmul, int ymul) {
        xmul = (xmul >>> 19);
        ymul = (ymul >>> 19);
        int accumA;
        int accumR;
        int accumG;
        int accumB;
        accumA = accumR = accumG = accumB = 0;
        for (int i = 0; i < 4; i++) {
            int rgb = rgbs[i];
            xmul = (1 << 12) - xmul;
            if ((i & 1) == 0) {
                ymul = (1 << 12) - ymul;
            }
            int factor = xmul * ymul;
            if (factor != 0) {
                accumA += (((rgb >>> 24)) * factor);
                accumR += (((rgb >>> 16) & 255) * factor);
                accumG += (((rgb >>> 8) & 255) * factor);
                accumB += (((rgb) & 255) * factor);
            }
        }
        return ((((accumA + (1 << 23)) >>> 24) << 24) | (((accumR + (1 << 23)) >>> 24) << 16) | (((accumG + (1 << 23)) >>> 24) << 8) | (((accumB + (1 << 23)) >>> 24)));
    }
    {
    }
    {
    }
    {
    }
    {
    }
}
