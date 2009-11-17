package java.awt.image;

import java.awt.image.ColorModel;

public abstract class RGBImageFilter extends ImageFilter {
    
    public RGBImageFilter() {
        
    }
    protected ColorModel origmodel;
    protected ColorModel newmodel;
    protected boolean canFilterIndexColorModel;
    
    public void setColorModel(ColorModel model) {
        if (canFilterIndexColorModel && (model instanceof IndexColorModel)) {
            ColorModel newcm = filterIndexColorModel((IndexColorModel)(IndexColorModel)model);
            substituteColorModel(model, newcm);
            consumer.setColorModel(newcm);
        } else {
            consumer.setColorModel(ColorModel.getRGBdefault());
        }
    }
    
    public void substituteColorModel(ColorModel oldcm, ColorModel newcm) {
        origmodel = oldcm;
        newmodel = newcm;
    }
    
    public IndexColorModel filterIndexColorModel(IndexColorModel icm) {
        int mapsize = icm.getMapSize();
        byte[] r = new byte[mapsize];
        byte[] g = new byte[mapsize];
        byte[] b = new byte[mapsize];
        byte[] a = new byte[mapsize];
        icm.getReds(r);
        icm.getGreens(g);
        icm.getBlues(b);
        icm.getAlphas(a);
        int trans = icm.getTransparentPixel();
        boolean needalpha = false;
        for (int i = 0; i < mapsize; i++) {
            int rgb = filterRGB(-1, -1, icm.getRGB(i));
            a[i] = (byte)(rgb >> 24);
            if (a[i] != ((byte)255) && i != trans) {
                needalpha = true;
            }
            r[i] = (byte)(rgb >> 16);
            g[i] = (byte)(rgb >> 8);
            b[i] = (byte)(rgb >> 0);
        }
        if (needalpha) {
            return new IndexColorModel(icm.getPixelSize(), mapsize, r, g, b, a);
        } else {
            return new IndexColorModel(icm.getPixelSize(), mapsize, r, g, b, trans);
        }
    }
    
    public void filterRGBPixels(int x, int y, int w, int h, int[] pixels, int off, int scansize) {
        int index = off;
        for (int cy = 0; cy < h; cy++) {
            for (int cx = 0; cx < w; cx++) {
                pixels[index] = filterRGB(x + cx, y + cy, pixels[index]);
                index++;
            }
            index += scansize - w;
        }
        consumer.setPixels(x, y, w, h, ColorModel.getRGBdefault(), pixels, off, scansize);
    }
    
    public void setPixels(int x, int y, int w, int h, ColorModel model, byte[] pixels, int off, int scansize) {
        if (model == origmodel) {
            consumer.setPixels(x, y, w, h, newmodel, pixels, off, scansize);
        } else {
            int[] filteredpixels = new int[w];
            int index = off;
            for (int cy = 0; cy < h; cy++) {
                for (int cx = 0; cx < w; cx++) {
                    filteredpixels[cx] = model.getRGB((pixels[index] & 255));
                    index++;
                }
                index += scansize - w;
                filterRGBPixels(x, y + cy, w, 1, filteredpixels, 0, w);
            }
        }
    }
    
    public void setPixels(int x, int y, int w, int h, ColorModel model, int[] pixels, int off, int scansize) {
        if (model == origmodel) {
            consumer.setPixels(x, y, w, h, newmodel, pixels, off, scansize);
        } else {
            int[] filteredpixels = new int[w];
            int index = off;
            for (int cy = 0; cy < h; cy++) {
                for (int cx = 0; cx < w; cx++) {
                    filteredpixels[cx] = model.getRGB(pixels[index]);
                    index++;
                }
                index += scansize - w;
                filterRGBPixels(x, y + cy, w, 1, filteredpixels, 0, w);
            }
        }
    }
    
    public abstract int filterRGB(int x, int y, int rgb);
}
