package java.awt.image;

import java.awt.image.ColorModel;

public class AreaAveragingScaleFilter extends ReplicateScaleFilter {
    private static final ColorModel rgbmodel = ColorModel.getRGBdefault();
    private static final int neededHints = (TOPDOWNLEFTRIGHT | COMPLETESCANLINES);
    private boolean passthrough;
    private float[] reds;
    private float[] greens;
    private float[] blues;
    private float[] alphas;
    private int savedy;
    private int savedyrem;
    
    public AreaAveragingScaleFilter(int width, int height) {
        super(width, height);
    }
    
    public void setHints(int hints) {
        passthrough = ((hints & neededHints) != neededHints);
        super.setHints(hints);
    }
    
    private void makeAccumBuffers() {
        reds = new float[destWidth];
        greens = new float[destWidth];
        blues = new float[destWidth];
        alphas = new float[destWidth];
    }
    
    private int[] calcRow() {
        float origmult = ((float)srcWidth) * srcHeight;
        if (outpixbuf == null || !(outpixbuf instanceof int[])) {
            outpixbuf = new int[destWidth];
        }
        int[] outpix = (int[])(int[])outpixbuf;
        for (int x = 0; x < destWidth; x++) {
            float mult = origmult;
            int a = Math.round(alphas[x] / mult);
            if (a <= 0) {
                a = 0;
            } else if (a >= 255) {
                a = 255;
            } else {
                mult = alphas[x] / 255;
            }
            int r = Math.round(reds[x] / mult);
            int g = Math.round(greens[x] / mult);
            int b = Math.round(blues[x] / mult);
            if (r < 0) {
                r = 0;
            } else if (r > 255) {
                r = 255;
            }
            if (g < 0) {
                g = 0;
            } else if (g > 255) {
                g = 255;
            }
            if (b < 0) {
                b = 0;
            } else if (b > 255) {
                b = 255;
            }
            outpix[x] = (a << 24 | r << 16 | g << 8 | b);
        }
        return outpix;
    }
    
    private void accumPixels(int x, int y, int w, int h, ColorModel model, Object pixels, int off, int scansize) {
        if (reds == null) {
            makeAccumBuffers();
        }
        int sy = y;
        int syrem = destHeight;
        int dy;
        int dyrem;
        if (sy == 0) {
            dy = 0;
            dyrem = 0;
        } else {
            dy = savedy;
            dyrem = savedyrem;
        }
        while (sy < y + h) {
            int amty;
            if (dyrem == 0) {
                for (int i = 0; i < destWidth; i++) {
                    alphas[i] = reds[i] = greens[i] = blues[i] = 0.0F;
                }
                dyrem = srcHeight;
            }
            if (syrem < dyrem) {
                amty = syrem;
            } else {
                amty = dyrem;
            }
            int sx = 0;
            int dx = 0;
            int sxrem = 0;
            int dxrem = srcWidth;
            float a = 0.0F;
            float r = 0.0F;
            float g = 0.0F;
            float b = 0.0F;
            while (sx < w) {
                if (sxrem == 0) {
                    sxrem = destWidth;
                    int rgb;
                    if (pixels instanceof byte[]) {
                        rgb = ((byte[])(byte[])pixels)[off + sx] & 255;
                    } else {
                        rgb = ((int[])(int[])pixels)[off + sx];
                    }
                    rgb = model.getRGB(rgb);
                    a = rgb >>> 24;
                    r = (rgb >> 16) & 255;
                    g = (rgb >> 8) & 255;
                    b = rgb & 255;
                    if (a != 255.0F) {
                        float ascale = a / 255.0F;
                        r *= ascale;
                        g *= ascale;
                        b *= ascale;
                    }
                }
                int amtx;
                if (sxrem < dxrem) {
                    amtx = sxrem;
                } else {
                    amtx = dxrem;
                }
                float mult = ((float)amtx) * amty;
                alphas[dx] += mult * a;
                reds[dx] += mult * r;
                greens[dx] += mult * g;
                blues[dx] += mult * b;
                if ((sxrem -= amtx) == 0) {
                    sx++;
                }
                if ((dxrem -= amtx) == 0) {
                    dx++;
                    dxrem = srcWidth;
                }
            }
            if ((dyrem -= amty) == 0) {
                int[] outpix = calcRow();
                do {
                    consumer.setPixels(0, dy, destWidth, 1, rgbmodel, outpix, 0, destWidth);
                    dy++;
                }                 while ((syrem -= amty) >= amty && amty == srcHeight);
            } else {
                syrem -= amty;
            }
            if (syrem == 0) {
                syrem = destHeight;
                sy++;
                off += scansize;
            }
        }
        savedyrem = dyrem;
        savedy = dy;
    }
    
    public void setPixels(int x, int y, int w, int h, ColorModel model, byte[] pixels, int off, int scansize) {
        if (passthrough) {
            super.setPixels(x, y, w, h, model, pixels, off, scansize);
        } else {
            accumPixels(x, y, w, h, model, pixels, off, scansize);
        }
    }
    
    public void setPixels(int x, int y, int w, int h, ColorModel model, int[] pixels, int off, int scansize) {
        if (passthrough) {
            super.setPixels(x, y, w, h, model, pixels, off, scansize);
        } else {
            accumPixels(x, y, w, h, model, pixels, off, scansize);
        }
    }
}
