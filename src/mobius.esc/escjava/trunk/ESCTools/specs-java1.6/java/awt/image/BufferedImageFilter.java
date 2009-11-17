package java.awt.image;

import java.awt.image.ImageFilter;

public class BufferedImageFilter extends ImageFilter implements Cloneable {
    BufferedImageOp bufferedImageOp;
    ColorModel model;
    int width;
    int height;
    byte[] bytePixels;
    int[] intPixels;
    
    public BufferedImageFilter(BufferedImageOp op) {
        
        if (op == null) {
            throw new NullPointerException("Operation cannot be null");
        }
        bufferedImageOp = op;
    }
    
    public BufferedImageOp getBufferedImageOp() {
        return bufferedImageOp;
    }
    
    public void setDimensions(int width, int height) {
        if (width <= 0 || height <= 0) {
            imageComplete(STATICIMAGEDONE);
            return;
        }
        this.width = width;
        this.height = height;
    }
    
    public void setColorModel(ColorModel model) {
        this.model = model;
    }
    
    private void convertToRGB() {
        int size = width * height;
        int[] newpixels = new int[size];
        if (bytePixels != null) {
            for (int i = 0; i < size; i++) {
                newpixels[i] = this.model.getRGB(bytePixels[i] & 255);
            }
        } else if (intPixels != null) {
            for (int i = 0; i < size; i++) {
                newpixels[i] = this.model.getRGB(intPixels[i]);
            }
        }
        bytePixels = null;
        intPixels = newpixels;
        this.model = ColorModel.getRGBdefault();
    }
    
    public void setPixels(int x, int y, int w, int h, ColorModel model, byte[] pixels, int off, int scansize) {
        if (w < 0 || h < 0) {
            throw new IllegalArgumentException("Width (" + w + ") and height (" + h + ") must be > 0");
        }
        if (w == 0 || h == 0) {
            return;
        }
        if (y < 0) {
            int diff = -y;
            if (diff >= h) {
                return;
            }
            off += scansize * diff;
            y += diff;
            h -= diff;
        }
        if (y + h > height) {
            h = height - y;
            if (h <= 0) {
                return;
            }
        }
        if (x < 0) {
            int diff = -x;
            if (diff >= w) {
                return;
            }
            off += diff;
            x += diff;
            w -= diff;
        }
        if (x + w > width) {
            w = width - x;
            if (w <= 0) {
                return;
            }
        }
        int dstPtr = y * width + x;
        if (intPixels == null) {
            if (bytePixels == null) {
                bytePixels = new byte[width * height];
                this.model = model;
            } else if (this.model != model) {
                convertToRGB();
            }
            if (bytePixels != null) {
                for (int sh = h; sh > 0; sh--) {
                    System.arraycopy(pixels, off, bytePixels, dstPtr, w);
                    off += scansize;
                    dstPtr += width;
                }
            }
        }
        if (intPixels != null) {
            int dstRem = width - w;
            int srcRem = scansize - w;
            for (int sh = h; sh > 0; sh--) {
                for (int sw = w; sw > 0; sw--) {
                    intPixels[dstPtr++] = model.getRGB(pixels[off++] & 255);
                }
                off += srcRem;
                dstPtr += dstRem;
            }
        }
    }
    
    public void setPixels(int x, int y, int w, int h, ColorModel model, int[] pixels, int off, int scansize) {
        if (w < 0 || h < 0) {
            throw new IllegalArgumentException("Width (" + w + ") and height (" + h + ") must be > 0");
        }
        if (w == 0 || h == 0) {
            return;
        }
        if (y < 0) {
            int diff = -y;
            if (diff >= h) {
                return;
            }
            off += scansize * diff;
            y += diff;
            h -= diff;
        }
        if (y + h > height) {
            h = height - y;
            if (h <= 0) {
                return;
            }
        }
        if (x < 0) {
            int diff = -x;
            if (diff >= w) {
                return;
            }
            off += diff;
            x += diff;
            w -= diff;
        }
        if (x + w > width) {
            w = width - x;
            if (w <= 0) {
                return;
            }
        }
        if (intPixels == null) {
            if (bytePixels == null) {
                intPixels = new int[width * height];
                this.model = model;
            } else {
                convertToRGB();
            }
        }
        int dstPtr = y * width + x;
        if (this.model == model) {
            for (int sh = h; sh > 0; sh--) {
                System.arraycopy(pixels, off, intPixels, dstPtr, w);
                off += scansize;
                dstPtr += width;
            }
        } else {
            if (this.model != ColorModel.getRGBdefault()) {
                convertToRGB();
            }
            int dstRem = width - w;
            int srcRem = scansize - w;
            for (int sh = h; sh > 0; sh--) {
                for (int sw = w; sw > 0; sw--) {
                    intPixels[dstPtr++] = model.getRGB(pixels[off++]);
                }
                off += srcRem;
                dstPtr += dstRem;
            }
        }
    }
    
    public void imageComplete(int status) {
        WritableRaster wr;
        switch (status) {
        case IMAGEERROR: 
        
        case IMAGEABORTED: 
            model = null;
            width = -1;
            height = -1;
            intPixels = null;
            bytePixels = null;
            break;
        
        case SINGLEFRAMEDONE: 
        
        case STATICIMAGEDONE: 
            if (width <= 0 || height <= 0) break;
            if (model instanceof DirectColorModel) {
                if (intPixels == null) break;
                wr = createDCMraster();
            } else if (model instanceof IndexColorModel) {
                int[] bandOffsets = {0};
                if (bytePixels == null) break;
                DataBufferByte db = new DataBufferByte(bytePixels, width * height);
                wr = Raster.createInterleavedRaster(db, width, height, width, 1, bandOffsets, null);
            } else {
                convertToRGB();
                if (intPixels == null) break;
                wr = createDCMraster();
            }
            BufferedImage bi = new BufferedImage(model, wr, model.isAlphaPremultiplied(), null);
            bi = bufferedImageOp.filter(bi, null);
            WritableRaster r = bi.getRaster();
            ColorModel cm = bi.getColorModel();
            int w = r.getWidth();
            int h = r.getHeight();
            consumer.setDimensions(w, h);
            consumer.setColorModel(cm);
            if (cm instanceof DirectColorModel) {
                DataBufferInt db = (DataBufferInt)(DataBufferInt)r.getDataBuffer();
                consumer.setPixels(0, 0, w, h, cm, db.getData(), 0, w);
            } else if (cm instanceof IndexColorModel) {
                DataBufferByte db = (DataBufferByte)(DataBufferByte)r.getDataBuffer();
                consumer.setPixels(0, 0, w, h, cm, db.getData(), 0, w);
            } else {
                throw new InternalError("Unknown color model " + cm);
            }
            break;
        
        }
        consumer.imageComplete(status);
    }
    
    private final WritableRaster createDCMraster() {
        WritableRaster wr;
        DirectColorModel dcm = (DirectColorModel)(DirectColorModel)model;
        boolean hasAlpha = model.hasAlpha();
        int[] bandMasks = new int[3 + (hasAlpha ? 1 : 0)];
        bandMasks[0] = dcm.getRedMask();
        bandMasks[1] = dcm.getGreenMask();
        bandMasks[2] = dcm.getBlueMask();
        if (hasAlpha) {
            bandMasks[3] = dcm.getAlphaMask();
        }
        DataBufferInt db = new DataBufferInt(intPixels, width * height);
        wr = Raster.createPackedRaster(db, width, height, width, bandMasks, null);
        return wr;
    }
}
