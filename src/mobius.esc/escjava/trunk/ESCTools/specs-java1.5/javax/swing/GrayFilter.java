package javax.swing;

import java.awt.*;
import java.awt.image.*;

public class GrayFilter extends RGBImageFilter {
    private boolean brighter;
    private int percent;
    
    public static Image createDisabledImage(Image i) {
        GrayFilter filter = new GrayFilter(true, 50);
        ImageProducer prod = new FilteredImageSource(i.getSource(), filter);
        Image grayImage = Toolkit.getDefaultToolkit().createImage(prod);
        return grayImage;
    }
    
    public GrayFilter(boolean b, int p) {
        
        brighter = b;
        percent = p;
        canFilterIndexColorModel = true;
    }
    
    public int filterRGB(int x, int y, int rgb) {
        int gray = (int)((0.3 * ((rgb >> 16) & 255) + 0.59 * ((rgb >> 8) & 255) + 0.11 * (rgb & 255)) / 3);
        if (brighter) {
            gray = (255 - ((255 - gray) * (100 - percent) / 100));
        } else {
            gray = (gray * (100 - percent) / 100);
        }
        if (gray < 0) gray = 0;
        if (gray > 255) gray = 255;
        return (rgb & -16777216) | (gray << 16) | (gray << 8) | (gray << 0);
    }
}
