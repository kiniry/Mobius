package java.awt;

import java.awt.image.WritableRaster;
import java.awt.image.ColorModel;
import java.awt.geom.AffineTransform;
import sun.awt.image.ByteInterleavedRaster;

class TexturePaintContext$Byte extends TexturePaintContext {
    ByteInterleavedRaster srcRas;
    byte[] inData;
    int inOff;
    int inSpan;
    byte[] outData;
    int outOff;
    int outSpan;
    
    public TexturePaintContext$Byte(ByteInterleavedRaster srcRas, ColorModel cm, AffineTransform xform, int maxw) {
        super(cm, xform, srcRas.getWidth(), srcRas.getHeight(), maxw);
        this.srcRas = srcRas;
        this.inData = srcRas.getDataStorage();
        this.inSpan = srcRas.getScanlineStride();
        this.inOff = srcRas.getDataOffset(0);
    }
    
    public WritableRaster makeRaster(int w, int h) {
        WritableRaster ras = makeByteRaster(srcRas, w, h);
        ByteInterleavedRaster biRas = (ByteInterleavedRaster)(ByteInterleavedRaster)ras;
        outData = biRas.getDataStorage();
        outSpan = biRas.getScanlineStride();
        outOff = biRas.getDataOffset(0);
        return ras;
    }
    
    public void dispose() {
        dropByteRaster(outRas);
    }
    
    public void setRaster(int x, int y, int xerr, int yerr, int w, int h, int bWidth, int bHeight, int colincx, int colincxerr, int colincy, int colincyerr, int rowincx, int rowincxerr, int rowincy, int rowincyerr) {
        byte[] inData = this.inData;
        byte[] outData = this.outData;
        int out = outOff;
        int inSpan = this.inSpan;
        int inOff = this.inOff;
        int outSpan = this.outSpan;
        boolean normalx = (colincx == 1 && colincxerr == 0 && colincy == 0 && colincyerr == 0);
        int rowx = x;
        int rowy = y;
        int rowxerr = xerr;
        int rowyerr = yerr;
        if (normalx) {
            outSpan -= w;
        }
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
                    outData[out + i] = inData[inOff + y * inSpan + x];
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
