package java.awt.image;

import java.awt.image.ColorModel;
import java.util.Hashtable;

public class ReplicateScaleFilter extends ImageFilter {
    protected int srcWidth;
    protected int srcHeight;
    protected int destWidth;
    protected int destHeight;
    protected int[] srcrows;
    protected int[] srccols;
    protected Object outpixbuf;
    
    public ReplicateScaleFilter(int width, int height) {
        
        if (width == 0 || height == 0) {
            throw new IllegalArgumentException("Width (" + width + ") and height (" + height + ") must be non-zero");
        }
        destWidth = width;
        destHeight = height;
    }
    
    public void setProperties(Hashtable props) {
        Hashtable p = (Hashtable)(Hashtable)props.clone();
        String key = "rescale";
        String val = destWidth + "x" + destHeight;
        Object o = p.get(key);
        if (o != null && o instanceof String) {
            val = ((String)(String)o) + ", " + val;
        }
        p.put(key, val);
        super.setProperties(p);
    }
    
    public void setDimensions(int w, int h) {
        srcWidth = w;
        srcHeight = h;
        if (destWidth < 0) {
            if (destHeight < 0) {
                destWidth = srcWidth;
                destHeight = srcHeight;
            } else {
                destWidth = srcWidth * destHeight / srcHeight;
            }
        } else if (destHeight < 0) {
            destHeight = srcHeight * destWidth / srcWidth;
        }
        consumer.setDimensions(destWidth, destHeight);
    }
    
    private void calculateMaps() {
        srcrows = new int[destHeight + 1];
        for (int y = 0; y <= destHeight; y++) {
            srcrows[y] = (2 * y * srcHeight + srcHeight) / (2 * destHeight);
        }
        srccols = new int[destWidth + 1];
        for (int x = 0; x <= destWidth; x++) {
            srccols[x] = (2 * x * srcWidth + srcWidth) / (2 * destWidth);
        }
    }
    
    public void setPixels(int x, int y, int w, int h, ColorModel model, byte[] pixels, int off, int scansize) {
        if (srcrows == null || srccols == null) {
            calculateMaps();
        }
        int sx;
        int sy;
        int dx1 = (2 * x * destWidth + srcWidth - 1) / (2 * srcWidth);
        int dy1 = (2 * y * destHeight + srcHeight - 1) / (2 * srcHeight);
        byte[] outpix;
        if (outpixbuf != null && outpixbuf instanceof byte[]) {
            outpix = (byte[])(byte[])outpixbuf;
        } else {
            outpix = new byte[destWidth];
            outpixbuf = outpix;
        }
        for (int dy = dy1; (sy = srcrows[dy]) < y + h; dy++) {
            int srcoff = off + scansize * (sy - y);
            int dx;
            for (dx = dx1; (sx = srccols[dx]) < x + w; dx++) {
                outpix[dx] = pixels[srcoff + sx - x];
            }
            if (dx > dx1) {
                consumer.setPixels(dx1, dy, dx - dx1, 1, model, outpix, dx1, destWidth);
            }
        }
    }
    
    public void setPixels(int x, int y, int w, int h, ColorModel model, int[] pixels, int off, int scansize) {
        if (srcrows == null || srccols == null) {
            calculateMaps();
        }
        int sx;
        int sy;
        int dx1 = (2 * x * destWidth + srcWidth - 1) / (2 * srcWidth);
        int dy1 = (2 * y * destHeight + srcHeight - 1) / (2 * srcHeight);
        int[] outpix;
        if (outpixbuf != null && outpixbuf instanceof int[]) {
            outpix = (int[])(int[])outpixbuf;
        } else {
            outpix = new int[destWidth];
            outpixbuf = outpix;
        }
        for (int dy = dy1; (sy = srcrows[dy]) < y + h; dy++) {
            int srcoff = off + scansize * (sy - y);
            int dx;
            for (dx = dx1; (sx = srccols[dx]) < x + w; dx++) {
                outpix[dx] = pixels[srcoff + sx - x];
            }
            if (dx > dx1) {
                consumer.setPixels(dx1, dy, dx - dx1, 1, model, outpix, dx1, destWidth);
            }
        }
    }
}
