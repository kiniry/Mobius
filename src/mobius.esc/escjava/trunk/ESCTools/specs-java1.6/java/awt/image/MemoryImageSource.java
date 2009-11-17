package java.awt.image;

import java.awt.image.ImageConsumer;
import java.awt.image.ImageProducer;
import java.awt.image.ColorModel;
import java.util.Hashtable;
import java.util.Vector;
import java.util.Enumeration;

public class MemoryImageSource implements ImageProducer {
    int width;
    int height;
    ColorModel model;
    Object pixels;
    int pixeloffset;
    int pixelscan;
    Hashtable properties;
    Vector theConsumers = new Vector();
    boolean animating;
    boolean fullbuffers;
    
    public MemoryImageSource(int w, int h, ColorModel cm, byte[] pix, int off, int scan) {
        
        initialize(w, h, cm, (Object)pix, off, scan, null);
    }
    
    public MemoryImageSource(int w, int h, ColorModel cm, byte[] pix, int off, int scan, Hashtable props) {
        
        initialize(w, h, cm, (Object)pix, off, scan, props);
    }
    
    public MemoryImageSource(int w, int h, ColorModel cm, int[] pix, int off, int scan) {
        
        initialize(w, h, cm, (Object)pix, off, scan, null);
    }
    
    public MemoryImageSource(int w, int h, ColorModel cm, int[] pix, int off, int scan, Hashtable props) {
        
        initialize(w, h, cm, (Object)pix, off, scan, props);
    }
    
    private void initialize(int w, int h, ColorModel cm, Object pix, int off, int scan, Hashtable props) {
        width = w;
        height = h;
        model = cm;
        pixels = pix;
        pixeloffset = off;
        pixelscan = scan;
        if (props == null) {
            props = new Hashtable();
        }
        properties = props;
    }
    
    public MemoryImageSource(int w, int h, int[] pix, int off, int scan) {
        
        initialize(w, h, ColorModel.getRGBdefault(), (Object)pix, off, scan, null);
    }
    
    public MemoryImageSource(int w, int h, int[] pix, int off, int scan, Hashtable props) {
        
        initialize(w, h, ColorModel.getRGBdefault(), (Object)pix, off, scan, props);
    }
    
    public synchronized void addConsumer(ImageConsumer ic) {
        if (theConsumers.contains(ic)) {
            return;
        }
        theConsumers.addElement(ic);
        try {
            initConsumer(ic);
            sendPixels(ic, 0, 0, width, height);
            if (isConsumer(ic)) {
                ic.imageComplete(animating ? ImageConsumer.SINGLEFRAMEDONE : ImageConsumer.STATICIMAGEDONE);
                if (!animating && isConsumer(ic)) {
                    ic.imageComplete(ImageConsumer.IMAGEERROR);
                    removeConsumer(ic);
                }
            }
        } catch (Exception e) {
            if (isConsumer(ic)) {
                ic.imageComplete(ImageConsumer.IMAGEERROR);
            }
        }
    }
    
    public synchronized boolean isConsumer(ImageConsumer ic) {
        return theConsumers.contains(ic);
    }
    
    public synchronized void removeConsumer(ImageConsumer ic) {
        theConsumers.removeElement(ic);
    }
    
    public void startProduction(ImageConsumer ic) {
        addConsumer(ic);
    }
    
    public void requestTopDownLeftRightResend(ImageConsumer ic) {
    }
    
    public synchronized void setAnimated(boolean animated) {
        this.animating = animated;
        if (!animating) {
            Enumeration enum_ = theConsumers.elements();
            while (enum_.hasMoreElements()) {
                ImageConsumer ic = (ImageConsumer)(ImageConsumer)enum_.nextElement();
                ic.imageComplete(ImageConsumer.STATICIMAGEDONE);
                if (isConsumer(ic)) {
                    ic.imageComplete(ImageConsumer.IMAGEERROR);
                }
            }
            theConsumers.removeAllElements();
        }
    }
    
    public synchronized void setFullBufferUpdates(boolean fullbuffers) {
        if (this.fullbuffers == fullbuffers) {
            return;
        }
        this.fullbuffers = fullbuffers;
        if (animating) {
            Enumeration enum_ = theConsumers.elements();
            while (enum_.hasMoreElements()) {
                ImageConsumer ic = (ImageConsumer)(ImageConsumer)enum_.nextElement();
                ic.setHints(fullbuffers ? (ImageConsumer.TOPDOWNLEFTRIGHT | ImageConsumer.COMPLETESCANLINES) : ImageConsumer.RANDOMPIXELORDER);
            }
        }
    }
    
    public void newPixels() {
        newPixels(0, 0, width, height, true);
    }
    
    public synchronized void newPixels(int x, int y, int w, int h) {
        newPixels(x, y, w, h, true);
    }
    
    public synchronized void newPixels(int x, int y, int w, int h, boolean framenotify) {
        if (animating) {
            if (fullbuffers) {
                x = y = 0;
                w = width;
                h = height;
            } else {
                if (x < 0) {
                    w += x;
                    x = 0;
                }
                if (x + w > width) {
                    w = width - x;
                }
                if (y < 0) {
                    h += y;
                    y = 0;
                }
                if (y + h > height) {
                    h = height - y;
                }
            }
            if ((w <= 0 || h <= 0) && !framenotify) {
                return;
            }
            Enumeration enum_ = theConsumers.elements();
            while (enum_.hasMoreElements()) {
                ImageConsumer ic = (ImageConsumer)(ImageConsumer)enum_.nextElement();
                if (w > 0 && h > 0) {
                    sendPixels(ic, x, y, w, h);
                }
                if (framenotify && isConsumer(ic)) {
                    ic.imageComplete(ImageConsumer.SINGLEFRAMEDONE);
                }
            }
        }
    }
    
    public synchronized void newPixels(byte[] newpix, ColorModel newmodel, int offset, int scansize) {
        this.pixels = newpix;
        this.model = newmodel;
        this.pixeloffset = offset;
        this.pixelscan = scansize;
        newPixels();
    }
    
    public synchronized void newPixels(int[] newpix, ColorModel newmodel, int offset, int scansize) {
        this.pixels = newpix;
        this.model = newmodel;
        this.pixeloffset = offset;
        this.pixelscan = scansize;
        newPixels();
    }
    
    private void initConsumer(ImageConsumer ic) {
        if (isConsumer(ic)) {
            ic.setDimensions(width, height);
        }
        if (isConsumer(ic)) {
            ic.setProperties(properties);
        }
        if (isConsumer(ic)) {
            ic.setColorModel(model);
        }
        if (isConsumer(ic)) {
            ic.setHints(animating ? (fullbuffers ? (ImageConsumer.TOPDOWNLEFTRIGHT | ImageConsumer.COMPLETESCANLINES) : ImageConsumer.RANDOMPIXELORDER) : (ImageConsumer.TOPDOWNLEFTRIGHT | ImageConsumer.COMPLETESCANLINES | ImageConsumer.SINGLEPASS | ImageConsumer.SINGLEFRAME));
        }
    }
    
    private void sendPixels(ImageConsumer ic, int x, int y, int w, int h) {
        int off = pixeloffset + pixelscan * y + x;
        if (isConsumer(ic)) {
            if (pixels instanceof byte[]) {
                ic.setPixels(x, y, w, h, model, ((byte[])(byte[])pixels), off, pixelscan);
            } else {
                ic.setPixels(x, y, w, h, model, ((int[])(int[])pixels), off, pixelscan);
            }
        }
    }
}
