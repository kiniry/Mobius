package java.awt.image;

import java.awt.Rectangle;
import java.awt.Point;

public class WritableRaster extends Raster {
    
    protected WritableRaster(SampleModel sampleModel, Point origin) {
        this(sampleModel, sampleModel.createDataBuffer(), new Rectangle(origin.x, origin.y, sampleModel.getWidth(), sampleModel.getHeight()), origin, null);
    }
    
    protected WritableRaster(SampleModel sampleModel, DataBuffer dataBuffer, Point origin) {
        this(sampleModel, dataBuffer, new Rectangle(origin.x, origin.y, sampleModel.getWidth(), sampleModel.getHeight()), origin, null);
    }
    
    protected WritableRaster(SampleModel sampleModel, DataBuffer dataBuffer, Rectangle aRegion, Point sampleModelTranslate, WritableRaster parent) {
        super(sampleModel, dataBuffer, aRegion, sampleModelTranslate, parent);
    }
    
    public WritableRaster getWritableParent() {
        return (WritableRaster)(WritableRaster)parent;
    }
    
    public WritableRaster createWritableTranslatedChild(int childMinX, int childMinY) {
        return createWritableChild(minX, minY, width, height, childMinX, childMinY, null);
    }
    
    public WritableRaster createWritableChild(int parentX, int parentY, int w, int h, int childMinX, int childMinY, int[] bandList) {
        if (parentX < this.minX) {
            throw new RasterFormatException("parentX lies outside raster");
        }
        if (parentY < this.minY) {
            throw new RasterFormatException("parentY lies outside raster");
        }
        if ((parentX + w < parentX) || (parentX + w > this.width + this.minX)) {
            throw new RasterFormatException("(parentX + width) is outside raster");
        }
        if ((parentY + h < parentY) || (parentY + h > this.height + this.minY)) {
            throw new RasterFormatException("(parentY + height) is outside raster");
        }
        SampleModel sm;
        if (bandList != null) {
            sm = sampleModel.createSubsetSampleModel(bandList);
        } else {
            sm = sampleModel;
        }
        int deltaX = childMinX - parentX;
        int deltaY = childMinY - parentY;
        return new WritableRaster(sm, getDataBuffer(), new Rectangle(childMinX, childMinY, w, h), new Point(sampleModelTranslateX + deltaX, sampleModelTranslateY + deltaY), this);
    }
    
    public void setDataElements(int x, int y, Object inData) {
        sampleModel.setDataElements(x - sampleModelTranslateX, y - sampleModelTranslateY, inData, dataBuffer);
    }
    
    public void setDataElements(int x, int y, Raster inRaster) {
        int dstOffX = x + inRaster.getMinX();
        int dstOffY = y + inRaster.getMinY();
        int width = inRaster.getWidth();
        int height = inRaster.getHeight();
        if ((dstOffX < this.minX) || (dstOffY < this.minY) || (dstOffX + width > this.minX + this.width) || (dstOffY + height > this.minY + this.height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        int srcOffX = inRaster.getMinX();
        int srcOffY = inRaster.getMinY();
        Object tdata = null;
        for (int startY = 0; startY < height; startY++) {
            tdata = inRaster.getDataElements(srcOffX, srcOffY + startY, width, 1, tdata);
            setDataElements(dstOffX, dstOffY + startY, width, 1, tdata);
        }
    }
    
    public void setDataElements(int x, int y, int w, int h, Object inData) {
        sampleModel.setDataElements(x - sampleModelTranslateX, y - sampleModelTranslateY, w, h, inData, dataBuffer);
    }
    
    public void setRect(Raster srcRaster) {
        setRect(0, 0, srcRaster);
    }
    
    public void setRect(int dx, int dy, Raster srcRaster) {
        int width = srcRaster.getWidth();
        int height = srcRaster.getHeight();
        int srcOffX = srcRaster.getMinX();
        int srcOffY = srcRaster.getMinY();
        int dstOffX = dx + srcOffX;
        int dstOffY = dy + srcOffY;
        if (dstOffX < this.minX) {
            int skipX = this.minX - dstOffX;
            width -= skipX;
            srcOffX += skipX;
            dstOffX = this.minX;
        }
        if (dstOffY < this.minY) {
            int skipY = this.minY - dstOffY;
            height -= skipY;
            srcOffY += skipY;
            dstOffY = this.minY;
        }
        if (dstOffX + width > this.minX + this.width) {
            width = this.minX + this.width - dstOffX;
        }
        if (dstOffY + height > this.minY + this.height) {
            height = this.minY + this.height - dstOffY;
        }
        if (width <= 0 || height <= 0) {
            return;
        }
        switch (srcRaster.getSampleModel().getDataType()) {
        case DataBuffer.TYPE_BYTE: 
        
        case DataBuffer.TYPE_SHORT: 
        
        case DataBuffer.TYPE_USHORT: 
        
        case DataBuffer.TYPE_INT: 
            int[] iData = null;
            for (int startY = 0; startY < height; startY++) {
                iData = srcRaster.getPixels(srcOffX, srcOffY + startY, width, 1, iData);
                setPixels(dstOffX, dstOffY + startY, width, 1, iData);
            }
            break;
        
        case DataBuffer.TYPE_FLOAT: 
            float[] fData = null;
            for (int startY = 0; startY < height; startY++) {
                fData = srcRaster.getPixels(srcOffX, srcOffY + startY, width, 1, fData);
                setPixels(dstOffX, dstOffY + startY, width, 1, fData);
            }
            break;
        
        case DataBuffer.TYPE_DOUBLE: 
            double[] dData = null;
            for (int startY = 0; startY < height; startY++) {
                dData = srcRaster.getPixels(srcOffX, srcOffY + startY, width, 1, dData);
                setPixels(dstOffX, dstOffY + startY, width, 1, dData);
            }
            break;
        
        }
    }
    
    public void setPixel(int x, int y, int[] iArray) {
        sampleModel.setPixel(x - sampleModelTranslateX, y - sampleModelTranslateY, iArray, dataBuffer);
    }
    
    public void setPixel(int x, int y, float[] fArray) {
        sampleModel.setPixel(x - sampleModelTranslateX, y - sampleModelTranslateY, fArray, dataBuffer);
    }
    
    public void setPixel(int x, int y, double[] dArray) {
        sampleModel.setPixel(x - sampleModelTranslateX, y - sampleModelTranslateY, dArray, dataBuffer);
    }
    
    public void setPixels(int x, int y, int w, int h, int[] iArray) {
        sampleModel.setPixels(x - sampleModelTranslateX, y - sampleModelTranslateY, w, h, iArray, dataBuffer);
    }
    
    public void setPixels(int x, int y, int w, int h, float[] fArray) {
        sampleModel.setPixels(x - sampleModelTranslateX, y - sampleModelTranslateY, w, h, fArray, dataBuffer);
    }
    
    public void setPixels(int x, int y, int w, int h, double[] dArray) {
        sampleModel.setPixels(x - sampleModelTranslateX, y - sampleModelTranslateY, w, h, dArray, dataBuffer);
    }
    
    public void setSample(int x, int y, int b, int s) {
        sampleModel.setSample(x - sampleModelTranslateX, y - sampleModelTranslateY, b, s, dataBuffer);
    }
    
    public void setSample(int x, int y, int b, float s) {
        sampleModel.setSample(x - sampleModelTranslateX, y - sampleModelTranslateY, b, s, dataBuffer);
    }
    
    public void setSample(int x, int y, int b, double s) {
        sampleModel.setSample(x - sampleModelTranslateX, y - sampleModelTranslateY, b, s, dataBuffer);
    }
    
    public void setSamples(int x, int y, int w, int h, int b, int[] iArray) {
        sampleModel.setSamples(x - sampleModelTranslateX, y - sampleModelTranslateY, w, h, b, iArray, dataBuffer);
    }
    
    public void setSamples(int x, int y, int w, int h, int b, float[] fArray) {
        sampleModel.setSamples(x - sampleModelTranslateX, y - sampleModelTranslateY, w, h, b, fArray, dataBuffer);
    }
    
    public void setSamples(int x, int y, int w, int h, int b, double[] dArray) {
        sampleModel.setSamples(x - sampleModelTranslateX, y - sampleModelTranslateY, w, h, b, dArray, dataBuffer);
    }
}
