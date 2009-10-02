package java.awt;

import java.awt.image.WritableRaster;
import java.awt.image.ColorModel;
import java.awt.geom.AffineTransform;
import sun.awt.image.IntegerInterleavedRaster;

class TexturePaintContext$Int extends TexturePaintContext {
    IntegerInterleavedRaster srcRas;
    int[] inData;
    int inOff;
    int inSpan;
    int[] outData;
    int outOff;
    int outSpan;
    boolean filter;
    
    public TexturePaintContext$Int(IntegerInterleavedRaster srcRas, ColorModel cm, AffineTransform xform, int maxw, boolean filter) {
        super(cm, xform, srcRas.getWidth(), srcRas.getHeight(), maxw);
        this.srcRas = srcRas;
        this.inData = srcRas.getDataStorage();
        this.inSpan = srcRas.getScanlineStride();
        this.inOff = srcRas.getDataOffset(0);
        this.filter = filter;
    }
    
    public WritableRaster makeRaster(int w, int h) {
        WritableRaster ras = makeRaster(colorModel, srcRas, w, h);
        IntegerInterleavedRaster iiRas = (IntegerInterleavedRaster)(IntegerInterleavedRaster)ras;
        outData = iiRas.getDataStorage();
        outSpan = iiRas.getScanlineStride();
        outOff = iiRas.getDataOffset(0);
        return ras;
    }
    
    public void setRaster(int x, int y, int xerr, int yerr, int w, int h, int bWidth, int bHeight, int colincx, int colincxerr, int colincy, int colincyerr, int rowincx, int rowincxerr, int rowincy, int rowincyerr) {
        int[] inData = this.inData;
        int[] outData = this.outData;
        int out = outOff;
        int inSpan = this.inSpan;
        int inOff = this.inOff;
        int outSpan = this.outSpan;
        boolean filter = this.filter;
        boolean normalx = (colincx == 1 && colincxerr == 0 && colincy == 0 && colincyerr == 0) && !filter;
        int rowx = x;
        int rowy = y;
        int rowxerr = xerr;
        int rowyerr = yerr;
        if (normalx) {
            outSpan -= w;
        }
        int[] rgbs = filter ? new int[4] : null;
        for (int j = 0; j < h; j++) {
            if (normalx) {
                int in = inOff + rowy * inSpan + bWidth;
                x = bWidth - rowx;
                out += w;
                if (bWidth >= 32) {
                    int i = w;
                    while (i > 0) {
                        int copyw = (i < x) ? i : x;
                        System.arraycopy(inData, in - x, outData, out - i, copyw);
                        i -= copyw;
                        if ((x -= copyw) == 0) {
                            x = bWidth;
                        }
                    }
                } else {
                    for (int i = w; i > 0; i--) {
                        outData[out - i] = inData[in - x];
                        if (--x == 0) {
                            x = bWidth;
                        }
                    }
                }
            } else {
                x = rowx;
                y = rowy;
                xerr = rowxerr;
                yerr = rowyerr;
                for (int i = 0; i < w; i++) {
                    if (filter) {
                        int nextx;
                        int nexty;
                        if ((nextx = x + 1) >= bWidth) {
                            nextx = 0;
                        }
                        if ((nexty = y + 1) >= bHeight) {
                            nexty = 0;
                        }
                        rgbs[0] = inData[inOff + y * inSpan + x];
                        rgbs[1] = inData[inOff + y * inSpan + nextx];
                        rgbs[2] = inData[inOff + nexty * inSpan + x];
                        rgbs[3] = inData[inOff + nexty * inSpan + nextx];
                        outData[out + i] = TexturePaintContext.blend(rgbs, xerr, yerr);
                    } else {
                        outData[out + i] = inData[inOff + y * inSpan + x];
                    }
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
