package java.awt;

import java.awt.image.WritableRaster;
import java.awt.image.ColorModel;
import java.awt.image.IndexColorModel;
import java.awt.geom.AffineTransform;
import sun.awt.image.IntegerInterleavedRaster;
import sun.awt.image.ByteInterleavedRaster;

class TexturePaintContext$ByteFilter extends TexturePaintContext {
    ByteInterleavedRaster srcRas;
    int[] inPalette;
    byte[] inData;
    int inOff;
    int inSpan;
    int[] outData;
    int outOff;
    int outSpan;
    
    public TexturePaintContext$ByteFilter(ByteInterleavedRaster srcRas, ColorModel cm, AffineTransform xform, int maxw) {
        super((cm.getTransparency() == Transparency.OPAQUE ? xrgbmodel : argbmodel), xform, srcRas.getWidth(), srcRas.getHeight(), maxw);
        this.inPalette = new int[256];
        ((IndexColorModel)(IndexColorModel)cm).getRGBs(this.inPalette);
        this.srcRas = srcRas;
        this.inData = srcRas.getDataStorage();
        this.inSpan = srcRas.getScanlineStride();
        this.inOff = srcRas.getDataOffset(0);
    }
    
    public WritableRaster makeRaster(int w, int h) {
        WritableRaster ras = makeRaster(colorModel, null, w, h);
        IntegerInterleavedRaster iiRas = (IntegerInterleavedRaster)(IntegerInterleavedRaster)ras;
        outData = iiRas.getDataStorage();
        outSpan = iiRas.getScanlineStride();
        outOff = iiRas.getDataOffset(0);
        return ras;
    }
    
    public void setRaster(int x, int y, int xerr, int yerr, int w, int h, int bWidth, int bHeight, int colincx, int colincxerr, int colincy, int colincyerr, int rowincx, int rowincxerr, int rowincy, int rowincyerr) {
        byte[] inData = this.inData;
        int[] outData = this.outData;
        int out = outOff;
        int inSpan = this.inSpan;
        int inOff = this.inOff;
        int outSpan = this.outSpan;
        int rowx = x;
        int rowy = y;
        int rowxerr = xerr;
        int rowyerr = yerr;
        int[] rgbs = new int[4];
        for (int j = 0; j < h; j++) {
            x = rowx;
            y = rowy;
            xerr = rowxerr;
            yerr = rowyerr;
            for (int i = 0; i < w; i++) {
                int nextx;
                int nexty;
                if ((nextx = x + 1) >= bWidth) {
                    nextx = 0;
                }
                if ((nexty = y + 1) >= bHeight) {
                    nexty = 0;
                }
                rgbs[0] = inPalette[255 & inData[inOff + x + inSpan * y]];
                rgbs[1] = inPalette[255 & inData[inOff + nextx + inSpan * y]];
                rgbs[2] = inPalette[255 & inData[inOff + x + inSpan * nexty]];
                rgbs[3] = inPalette[255 & inData[inOff + nextx + inSpan * nexty]];
                outData[out + i] = TexturePaintContext.blend(rgbs, xerr, yerr);
                if ((xerr += colincxerr) < 0) {
                    xerr &= Integer.MAX_VALUE;
                    x++;
                }
                if ((x += colincx) >= bWidth) {
                    x -= bWidth;
                }
                if ((yerr += colincyerr) < 0) {
                    yerr &= Integer.MAX_VALUE;
                    y++;
                }
                if ((y += colincy) >= bHeight) {
                    y -= bHeight;
                }
            }
            if ((rowxerr += rowincxerr) < 0) {
                rowxerr &= Integer.MAX_VALUE;
                rowx++;
            }
            if ((rowx += rowincx) >= bWidth) {
                rowx -= bWidth;
            }
            if ((rowyerr += rowincyerr) < 0) {
                rowyerr &= Integer.MAX_VALUE;
                rowy++;
            }
            if ((rowy += rowincy) >= bHeight) {
                rowy -= bHeight;
            }
            out += outSpan;
        }
    }
}
