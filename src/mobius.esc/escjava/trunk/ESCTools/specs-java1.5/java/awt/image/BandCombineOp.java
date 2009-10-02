package java.awt.image;

import java.awt.geom.Rectangle2D;
import java.awt.geom.Point2D;
import java.awt.RenderingHints;
import sun.awt.image.ImagingLib;

public class BandCombineOp implements RasterOp {
    float[][] matrix;
    int nrows = 0;
    int ncols = 0;
    RenderingHints hints;
    
    public BandCombineOp(float[][] matrix, RenderingHints hints) {
        
        nrows = matrix.length;
        ncols = matrix[0].length;
        this.matrix = new float[nrows][ncols + 1];
        for (int i = 0; i < nrows; i++) {
            System.arraycopy(matrix[i], 0, this.matrix[i], 0, ncols);
        }
        this.hints = hints;
    }
    
    public final float[][] getMatrix() {
        return (float[][])(float[][])matrix.clone();
    }
    
    public WritableRaster filter(Raster src, WritableRaster dst) {
        int nBands = src.getNumBands();
        if (ncols != nBands && ncols != (nBands + 1)) {
            throw new IllegalArgumentException("Number of columns in the " + "matrix (" + ncols + ") must be equal to the number" + " of bands ([+1]) in src (" + nBands + ").");
        }
        if (dst == null) {
            dst = createCompatibleDestRaster(src);
        } else if (nrows != dst.getNumBands()) {
            throw new IllegalArgumentException("Number of rows in the " + "matrix (" + nrows + ") must be equal to the number" + " of bands ([+1]) in dst (" + nBands + ").");
        }
        if (ImagingLib.filter(this, src, dst) != null) {
            return dst;
        }
        int[] pixel = null;
        int[] dstPixel = new int[dst.getNumBands()];
        float accum;
        int sminX = src.getMinX();
        int sY = src.getMinY();
        int dminX = dst.getMinX();
        int dY = dst.getMinY();
        int sX;
        int dX;
        if (ncols == nBands) {
            for (int y = 0; y < src.getHeight(); y++, sY++, dY++) {
                dX = dminX;
                sX = sminX;
                for (int x = 0; x < src.getWidth(); x++, sX++, dX++) {
                    pixel = src.getPixel(sX, sY, pixel);
                    for (int r = 0; r < nrows; r++) {
                        accum = 0.0F;
                        for (int c = 0; c < ncols; c++) {
                            accum += matrix[r][c] * pixel[c];
                        }
                        dstPixel[r] = (int)accum;
                    }
                    dst.setPixel(dX, dY, dstPixel);
                }
            }
        } else {
            for (int y = 0; y < src.getHeight(); y++, sY++, dY++) {
                dX = dminX;
                sX = sminX;
                for (int x = 0; x < src.getWidth(); x++, sX++, dX++) {
                    pixel = src.getPixel(sX, sY, pixel);
                    for (int r = 0; r < nrows; r++) {
                        accum = 0.0F;
                        for (int c = 0; c < nBands; c++) {
                            accum += matrix[r][c] * pixel[c];
                        }
                        dstPixel[r] = (int)(accum + matrix[r][nBands]);
                    }
                    dst.setPixel(dX, dY, dstPixel);
                }
            }
        }
        return dst;
    }
    
    public final Rectangle2D getBounds2D(Raster src) {
        return src.getBounds();
    }
    
    public WritableRaster createCompatibleDestRaster(Raster src) {
        int nBands = src.getNumBands();
        if ((ncols != nBands) && (ncols != (nBands + 1))) {
            throw new IllegalArgumentException("Number of columns in the " + "matrix (" + ncols + ") must be equal to the number" + " of bands ([+1]) in src (" + nBands + ").");
        }
        if (src.getNumBands() == nrows) {
            return src.createCompatibleWritableRaster();
        } else {
            throw new IllegalArgumentException("Don\'t know how to create a " + " compatible Raster with " + nrows + " bands.");
        }
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
