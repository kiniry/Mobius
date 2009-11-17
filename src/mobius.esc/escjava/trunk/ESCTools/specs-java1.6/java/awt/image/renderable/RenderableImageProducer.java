package java.awt.image.renderable;

import java.awt.image.ColorModel;
import java.awt.image.DataBuffer;
import java.awt.image.ImageConsumer;
import java.awt.image.ImageProducer;
import java.awt.image.Raster;
import java.awt.image.RenderedImage;
import java.awt.image.SampleModel;
import java.util.Enumeration;
import java.util.Vector;

public class RenderableImageProducer implements ImageProducer, Runnable {
    RenderableImage rdblImage;
    RenderContext rc;
    Vector ics = new Vector();
    
    public RenderableImageProducer(RenderableImage rdblImage, RenderContext rc) {
        
        this.rdblImage = rdblImage;
        this.rc = rc;
    }
    
    public synchronized void setRenderContext(RenderContext rc) {
        this.rc = rc;
    }
    
    public synchronized void addConsumer(ImageConsumer ic) {
        if (!ics.contains(ic)) {
            ics.addElement(ic);
        }
    }
    
    public synchronized boolean isConsumer(ImageConsumer ic) {
        return ics.contains(ic);
    }
    
    public synchronized void removeConsumer(ImageConsumer ic) {
        ics.removeElement(ic);
    }
    
    public synchronized void startProduction(ImageConsumer ic) {
        addConsumer(ic);
        Thread thread = new Thread(this, "RenderableImageProducer Thread");
        thread.start();
    }
    
    public void requestTopDownLeftRightResend(ImageConsumer ic) {
    }
    
    public void run() {
        RenderedImage rdrdImage;
        if (rc != null) {
            rdrdImage = rdblImage.createRendering(rc);
        } else {
            rdrdImage = rdblImage.createDefaultRendering();
        }
        ColorModel colorModel = rdrdImage.getColorModel();
        Raster raster = rdrdImage.getData();
        SampleModel sampleModel = raster.getSampleModel();
        DataBuffer dataBuffer = raster.getDataBuffer();
        if (colorModel == null) {
            colorModel = ColorModel.getRGBdefault();
        }
        int minX = raster.getMinX();
        int minY = raster.getMinY();
        int width = raster.getWidth();
        int height = raster.getHeight();
        Enumeration icList;
        ImageConsumer ic;
        icList = ics.elements();
        while (icList.hasMoreElements()) {
            ic = (ImageConsumer)(ImageConsumer)icList.nextElement();
            ic.setDimensions(width, height);
            ic.setHints(ImageConsumer.TOPDOWNLEFTRIGHT | ImageConsumer.COMPLETESCANLINES | ImageConsumer.SINGLEPASS | ImageConsumer.SINGLEFRAME);
        }
        int[] pix = new int[width];
        int i;
        int j;
        int numBands = sampleModel.getNumBands();
        int[] tmpPixel = new int[numBands];
        for (j = 0; j < height; j++) {
            for (i = 0; i < width; i++) {
                sampleModel.getPixel(i, j, tmpPixel, dataBuffer);
                pix[i] = colorModel.getDataElement(tmpPixel, 0);
            }
            icList = ics.elements();
            while (icList.hasMoreElements()) {
                ic = (ImageConsumer)(ImageConsumer)icList.nextElement();
                ic.setPixels(0, j, width, 1, colorModel, pix, 0, width);
            }
        }
        icList = ics.elements();
        while (icList.hasMoreElements()) {
            ic = (ImageConsumer)(ImageConsumer)icList.nextElement();
            ic.imageComplete(ImageConsumer.STATICIMAGEDONE);
        }
    }
}
