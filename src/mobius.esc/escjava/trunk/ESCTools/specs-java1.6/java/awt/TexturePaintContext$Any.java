package java.awt;

import java.awt.image.WritableRaster;
import java.awt.image.ColorModel;
import java.awt.geom.AffineTransform;

class TexturePaintContext$Any extends TexturePaintContext {
    WritableRaster srcRas;
    boolean filter;
    
    public TexturePaintContext$Any(WritableRaster srcRas, ColorModel cm, AffineTransform xform, int maxw, boolean filter) {
        super(cm, xform, srcRas.getWidth(), srcRas.getHeight(), maxw);
        this.srcRas = srcRas;
        this.filter = filter;
    }
    
    public WritableRaster makeRaster(int w, int h) {
        return makeRaster(colorModel, srcRas, w, h);
    }
    
    public void setRaster(int x, int y, int xerr, int yerr, int w, int h, int bWidth, int bHeight, int colincx, int colincxerr, int colincy, int colincyerr, int rowincx, int rowincxerr, int rowincy, int rowincyerr) {
        Object data = null;
        int rowx = x;
        int rowy = y;
        int rowxerr = xerr;
        int rowyerr = yerr;
        WritableRaster srcRas = this.srcRas;
        WritableRaster outRas = this.outRas;
        int[] rgbs = filter ? new int[4] : null;
        for (int j = 0; j < h; j++) {
            x = rowx;
            y = rowy;
            xerr = rowxerr;
            yerr = rowyerr;
            for (int i = 0; i < w; i++) {
                data = srcRas.getDataElements(x, y, data);
                if (filter) {
                    int nextx;
                    int nexty;
                    if ((nextx = x + 1) >= bWidth) {
                        nextx = 0;
                    }
                    if ((nexty = y + 1) >= bHeight) {
                        nexty = 0;
                    }
                    rgbs[0] = colorModel.getRGB(data);
                    data = srcRas.getDataElements(nextx, y, data);
                    rgbs[1] = colorModel.getRGB(data);
                    data = srcRas.getDataElements(x, nexty, data);
                    rgbs[2] = colorModel.getRGB(data);
                    data = srcRas.getDataElements(nextx, nexty, data);
                    rgbs[3] = colorModel.getRGB(data);
                    int rgb = TexturePaintContext.blend(rgbs, xerr, yerr);
                    data = colorModel.getDataElements(rgb, data);
                }
                outRas.setDataElements(i, j, data);
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
        }
    }
}
