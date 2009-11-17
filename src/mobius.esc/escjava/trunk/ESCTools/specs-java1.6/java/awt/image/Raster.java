package java.awt.image;

import java.awt.Rectangle;
import java.awt.Point;
import sun.awt.image.ByteInterleavedRaster;
import sun.awt.image.ShortInterleavedRaster;
import sun.awt.image.IntegerInterleavedRaster;
import sun.awt.image.ByteBandedRaster;
import sun.awt.image.ShortBandedRaster;
import sun.awt.image.BytePackedRaster;
import sun.awt.image.SunWritableRaster;

public class Raster {
    protected SampleModel sampleModel;
    protected DataBuffer dataBuffer;
    protected int minX;
    protected int minY;
    protected int width;
    protected int height;
    protected int sampleModelTranslateX;
    protected int sampleModelTranslateY;
    protected int numBands;
    protected int numDataElements;
    protected Raster parent;
    
    private static native void initIDs();
    static {
        ColorModel.loadLibraries();
        initIDs();
    }
    
    public static WritableRaster createInterleavedRaster(int dataType, int w, int h, int bands, Point location) {
        int[] bandOffsets = new int[bands];
        for (int i = 0; i < bands; i++) {
            bandOffsets[i] = i;
        }
        return createInterleavedRaster(dataType, w, h, w * bands, bands, bandOffsets, location);
    }
    
    public static WritableRaster createInterleavedRaster(int dataType, int w, int h, int scanlineStride, int pixelStride, int[] bandOffsets, Point location) {
        DataBuffer d;
        int bands = bandOffsets.length;
        int maxBandOff = bandOffsets[0];
        for (int i = 1; i < bands; i++) {
            if (bandOffsets[i] > maxBandOff) {
                maxBandOff = bandOffsets[i];
            }
        }
        int size = maxBandOff + scanlineStride * (h - 1) + pixelStride * (w - 1) + 1;
        switch (dataType) {
        case DataBuffer.TYPE_BYTE: 
            d = new DataBufferByte(size);
            break;
        
        case DataBuffer.TYPE_USHORT: 
            d = new DataBufferUShort(size);
            break;
        
        default: 
            throw new IllegalArgumentException("Unsupported data type " + dataType);
        
        }
        SunWritableRaster raster = (SunWritableRaster)(SunWritableRaster)createInterleavedRaster(d, w, h, scanlineStride, pixelStride, bandOffsets, location);
        raster.setStolen(false);
        return raster;
    }
    
    public static WritableRaster createBandedRaster(int dataType, int w, int h, int bands, Point location) {
        if (bands < 1) {
            throw new ArrayIndexOutOfBoundsException("Number of bands (" + bands + ") must" + " be greater than 0");
        }
        int[] bankIndices = new int[bands];
        int[] bandOffsets = new int[bands];
        for (int i = 0; i < bands; i++) {
            bankIndices[i] = i;
            bandOffsets[i] = 0;
        }
        return createBandedRaster(dataType, w, h, w, bankIndices, bandOffsets, location);
    }
    
    public static WritableRaster createBandedRaster(int dataType, int w, int h, int scanlineStride, int[] bankIndices, int[] bandOffsets, Point location) {
        DataBuffer d;
        int bands = bandOffsets.length;
        if (bankIndices == null) {
            throw new ArrayIndexOutOfBoundsException("Bank indices array is null");
        }
        if (bandOffsets == null) {
            throw new ArrayIndexOutOfBoundsException("Band offsets array is null");
        }
        int maxBank = bankIndices[0];
        int maxBandOff = bandOffsets[0];
        for (int i = 1; i < bands; i++) {
            if (bankIndices[i] > maxBank) {
                maxBank = bankIndices[i];
            }
            if (bandOffsets[i] > maxBandOff) {
                maxBandOff = bandOffsets[i];
            }
        }
        int banks = maxBank + 1;
        int size = maxBandOff + scanlineStride * (h - 1) + (w - 1) + 1;
        switch (dataType) {
        case DataBuffer.TYPE_BYTE: 
            d = new DataBufferByte(size, banks);
            break;
        
        case DataBuffer.TYPE_USHORT: 
            d = new DataBufferUShort(size, banks);
            break;
        
        case DataBuffer.TYPE_INT: 
            d = new DataBufferInt(size, banks);
            break;
        
        default: 
            throw new IllegalArgumentException("Unsupported data type " + dataType);
        
        }
        SunWritableRaster raster = (SunWritableRaster)(SunWritableRaster)createBandedRaster(d, w, h, scanlineStride, bankIndices, bandOffsets, location);
        raster.setStolen(false);
        return raster;
    }
    
    public static WritableRaster createPackedRaster(int dataType, int w, int h, int[] bandMasks, Point location) {
        DataBuffer d;
        switch (dataType) {
        case DataBuffer.TYPE_BYTE: 
            d = new DataBufferByte(w * h);
            break;
        
        case DataBuffer.TYPE_USHORT: 
            d = new DataBufferUShort(w * h);
            break;
        
        case DataBuffer.TYPE_INT: 
            d = new DataBufferInt(w * h);
            break;
        
        default: 
            throw new IllegalArgumentException("Unsupported data type " + dataType);
        
        }
        SunWritableRaster raster = (SunWritableRaster)(SunWritableRaster)createPackedRaster(d, w, h, w, bandMasks, location);
        raster.setStolen(false);
        return raster;
    }
    
    public static WritableRaster createPackedRaster(int dataType, int w, int h, int bands, int bitsPerBand, Point location) {
        DataBuffer d;
        if (bands <= 0) {
            throw new IllegalArgumentException("Number of bands (" + bands + ") must be greater than 0");
        }
        if (bitsPerBand <= 0) {
            throw new IllegalArgumentException("Bits per band (" + bitsPerBand + ") must be greater than 0");
        }
        if (bands != 1) {
            int[] masks = new int[bands];
            int mask = (1 << bitsPerBand) - 1;
            int shift = (bands - 1) * bitsPerBand;
            if (shift + bitsPerBand > DataBuffer.getDataTypeSize(dataType)) {
                throw new IllegalArgumentException("bitsPerBand(" + bitsPerBand + ") * bands is " + " greater than data type " + "size.");
            }
            switch (dataType) {
            case DataBuffer.TYPE_BYTE: 
            
            case DataBuffer.TYPE_USHORT: 
            
            case DataBuffer.TYPE_INT: 
                break;
            
            default: 
                throw new IllegalArgumentException("Unsupported data type " + dataType);
            
            }
            for (int i = 0; i < bands; i++) {
                masks[i] = mask << shift;
                shift = shift - bitsPerBand;
            }
            return createPackedRaster(dataType, w, h, masks, location);
        } else {
            double fw = w;
            switch (dataType) {
            case DataBuffer.TYPE_BYTE: 
                d = new DataBufferByte((int)(Math.ceil(fw / (8 / bitsPerBand))) * h);
                break;
            
            case DataBuffer.TYPE_USHORT: 
                d = new DataBufferUShort((int)(Math.ceil(fw / (16 / bitsPerBand))) * h);
                break;
            
            case DataBuffer.TYPE_INT: 
                d = new DataBufferInt((int)(Math.ceil(fw / (32 / bitsPerBand))) * h);
                break;
            
            default: 
                throw new IllegalArgumentException("Unsupported data type " + dataType);
            
            }
            SunWritableRaster raster = (SunWritableRaster)(SunWritableRaster)createPackedRaster(d, w, h, bitsPerBand, location);
            raster.setStolen(false);
            return raster;
        }
    }
    
    public static WritableRaster createInterleavedRaster(DataBuffer dataBuffer, int w, int h, int scanlineStride, int pixelStride, int[] bandOffsets, Point location) {
        if (dataBuffer == null) {
            throw new NullPointerException("DataBuffer cannot be null");
        }
        if (location == null) {
            location = new Point(0, 0);
        }
        int dataType = dataBuffer.getDataType();
        PixelInterleavedSampleModel csm = new PixelInterleavedSampleModel(dataType, w, h, pixelStride, scanlineStride, bandOffsets);
        switch (dataType) {
        case DataBuffer.TYPE_BYTE: 
            return new ByteInterleavedRaster(csm, dataBuffer, location);
        
        case DataBuffer.TYPE_USHORT: 
            return new ShortInterleavedRaster(csm, dataBuffer, location);
        
        default: 
            throw new IllegalArgumentException("Unsupported data type " + dataType);
        
        }
    }
    
    public static WritableRaster createBandedRaster(DataBuffer dataBuffer, int w, int h, int scanlineStride, int[] bankIndices, int[] bandOffsets, Point location) {
        if (dataBuffer == null) {
            throw new NullPointerException("DataBuffer cannot be null");
        }
        if (location == null) {
            location = new Point(0, 0);
        }
        int dataType = dataBuffer.getDataType();
        int bands = bankIndices.length;
        if (bandOffsets.length != bands) {
            throw new IllegalArgumentException("bankIndices.length != bandOffsets.length");
        }
        BandedSampleModel bsm = new BandedSampleModel(dataType, w, h, scanlineStride, bankIndices, bandOffsets);
        switch (dataType) {
        case DataBuffer.TYPE_BYTE: 
            return new ByteBandedRaster(bsm, dataBuffer, location);
        
        case DataBuffer.TYPE_USHORT: 
            return new ShortBandedRaster(bsm, dataBuffer, location);
        
        case DataBuffer.TYPE_INT: 
            return new SunWritableRaster(bsm, dataBuffer, location);
        
        default: 
            throw new IllegalArgumentException("Unsupported data type " + dataType);
        
        }
    }
    
    public static WritableRaster createPackedRaster(DataBuffer dataBuffer, int w, int h, int scanlineStride, int[] bandMasks, Point location) {
        if (dataBuffer == null) {
            throw new NullPointerException("DataBuffer cannot be null");
        }
        if (location == null) {
            location = new Point(0, 0);
        }
        int dataType = dataBuffer.getDataType();
        SinglePixelPackedSampleModel sppsm = new SinglePixelPackedSampleModel(dataType, w, h, scanlineStride, bandMasks);
        switch (dataType) {
        case DataBuffer.TYPE_BYTE: 
            return new ByteInterleavedRaster(sppsm, dataBuffer, location);
        
        case DataBuffer.TYPE_USHORT: 
            return new ShortInterleavedRaster(sppsm, dataBuffer, location);
        
        case DataBuffer.TYPE_INT: 
            return new IntegerInterleavedRaster(sppsm, dataBuffer, location);
        
        default: 
            throw new IllegalArgumentException("Unsupported data type " + dataType);
        
        }
    }
    
    public static WritableRaster createPackedRaster(DataBuffer dataBuffer, int w, int h, int bitsPerPixel, Point location) {
        if (dataBuffer == null) {
            throw new NullPointerException("DataBuffer cannot be null");
        }
        if (location == null) {
            location = new Point(0, 0);
        }
        int dataType = dataBuffer.getDataType();
        if (dataType != DataBuffer.TYPE_BYTE && dataType != DataBuffer.TYPE_USHORT && dataType != DataBuffer.TYPE_INT) {
            throw new IllegalArgumentException("Unsupported data type " + dataType);
        }
        if (dataBuffer.getNumBanks() != 1) {
            throw new RasterFormatException("DataBuffer for packed Rasters must only have 1 bank.");
        }
        MultiPixelPackedSampleModel mppsm = new MultiPixelPackedSampleModel(dataType, w, h, bitsPerPixel);
        if (dataType == DataBuffer.TYPE_BYTE && (bitsPerPixel == 1 || bitsPerPixel == 2 || bitsPerPixel == 4)) {
            return new BytePackedRaster(mppsm, dataBuffer, location);
        } else {
            return new SunWritableRaster(mppsm, dataBuffer, location);
        }
    }
    
    public static Raster createRaster(SampleModel sm, DataBuffer db, Point location) {
        if ((sm == null) || (db == null)) {
            throw new NullPointerException("SampleModel and DataBuffer cannot be null");
        }
        if (location == null) {
            location = new Point(0, 0);
        }
        int dataType = sm.getDataType();
        if (sm instanceof PixelInterleavedSampleModel) {
            switch (dataType) {
            case DataBuffer.TYPE_BYTE: 
                return new ByteInterleavedRaster(sm, db, location);
            
            case DataBuffer.TYPE_USHORT: 
                return new ShortInterleavedRaster(sm, db, location);
            
            }
        } else if (sm instanceof SinglePixelPackedSampleModel) {
            switch (dataType) {
            case DataBuffer.TYPE_BYTE: 
                return new ByteInterleavedRaster(sm, db, location);
            
            case DataBuffer.TYPE_USHORT: 
                return new ShortInterleavedRaster(sm, db, location);
            
            case DataBuffer.TYPE_INT: 
                return new IntegerInterleavedRaster(sm, db, location);
            
            }
        } else if (sm instanceof MultiPixelPackedSampleModel && dataType == DataBuffer.TYPE_BYTE && sm.getSampleSize(0) < 8) {
            return new BytePackedRaster(sm, db, location);
        }
        return new Raster(sm, db, location);
    }
    
    public static WritableRaster createWritableRaster(SampleModel sm, Point location) {
        if (location == null) {
            location = new Point(0, 0);
        }
        SunWritableRaster raster = (SunWritableRaster)(SunWritableRaster)createWritableRaster(sm, sm.createDataBuffer(), location);
        raster.setStolen(false);
        return raster;
    }
    
    public static WritableRaster createWritableRaster(SampleModel sm, DataBuffer db, Point location) {
        if ((sm == null) || (db == null)) {
            throw new NullPointerException("SampleModel and DataBuffer cannot be null");
        }
        if (location == null) {
            location = new Point(0, 0);
        }
        int dataType = sm.getDataType();
        if (sm instanceof PixelInterleavedSampleModel) {
            switch (dataType) {
            case DataBuffer.TYPE_BYTE: 
                return new ByteInterleavedRaster(sm, db, location);
            
            case DataBuffer.TYPE_USHORT: 
                return new ShortInterleavedRaster(sm, db, location);
            
            }
        } else if (sm instanceof SinglePixelPackedSampleModel) {
            switch (dataType) {
            case DataBuffer.TYPE_BYTE: 
                return new ByteInterleavedRaster(sm, db, location);
            
            case DataBuffer.TYPE_USHORT: 
                return new ShortInterleavedRaster(sm, db, location);
            
            case DataBuffer.TYPE_INT: 
                return new IntegerInterleavedRaster(sm, db, location);
            
            }
        } else if (sm instanceof MultiPixelPackedSampleModel && dataType == DataBuffer.TYPE_BYTE && sm.getSampleSize(0) < 8) {
            return new BytePackedRaster(sm, db, location);
        }
        return new SunWritableRaster(sm, db, location);
    }
    
    protected Raster(SampleModel sampleModel, Point origin) {
        this(sampleModel, sampleModel.createDataBuffer(), new Rectangle(origin.x, origin.y, sampleModel.getWidth(), sampleModel.getHeight()), origin, null);
    }
    
    protected Raster(SampleModel sampleModel, DataBuffer dataBuffer, Point origin) {
        this(sampleModel, dataBuffer, new Rectangle(origin.x, origin.y, sampleModel.getWidth(), sampleModel.getHeight()), origin, null);
    }
    
    protected Raster(SampleModel sampleModel, DataBuffer dataBuffer, Rectangle aRegion, Point sampleModelTranslate, Raster parent) {
        
        if ((sampleModel == null) || (dataBuffer == null) || (aRegion == null) || (sampleModelTranslate == null)) {
            throw new NullPointerException("SampleModel, dataBuffer, aRegion and sampleModelTranslate cannot be null");
        }
        this.sampleModel = sampleModel;
        this.dataBuffer = dataBuffer;
        minX = aRegion.x;
        minY = aRegion.y;
        width = aRegion.width;
        height = aRegion.height;
        if (width <= 0 || height <= 0) {
            throw new RasterFormatException("negative or zero " + ((width <= 0) ? "width" : "height"));
        }
        if ((minX + width) < minX) {
            throw new RasterFormatException("overflow condition for X coordinates of Raster");
        }
        if ((minY + height) < minY) {
            throw new RasterFormatException("overflow condition for Y coordinates of Raster");
        }
        sampleModelTranslateX = sampleModelTranslate.x;
        sampleModelTranslateY = sampleModelTranslate.y;
        numBands = sampleModel.getNumBands();
        numDataElements = sampleModel.getNumDataElements();
        this.parent = parent;
    }
    
    public Raster getParent() {
        return parent;
    }
    
    public final int getSampleModelTranslateX() {
        return sampleModelTranslateX;
    }
    
    public final int getSampleModelTranslateY() {
        return sampleModelTranslateY;
    }
    
    public WritableRaster createCompatibleWritableRaster() {
        return new SunWritableRaster(sampleModel, new Point(0, 0));
    }
    
    public WritableRaster createCompatibleWritableRaster(int w, int h) {
        if (w <= 0 || h <= 0) {
            throw new RasterFormatException("negative " + ((w <= 0) ? "width" : "height"));
        }
        SampleModel sm = sampleModel.createCompatibleSampleModel(w, h);
        return new SunWritableRaster(sm, new Point(0, 0));
    }
    
    public WritableRaster createCompatibleWritableRaster(Rectangle rect) {
        if (rect == null) {
            throw new NullPointerException("Rect cannot be null");
        }
        return createCompatibleWritableRaster(rect.x, rect.y, rect.width, rect.height);
    }
    
    public WritableRaster createCompatibleWritableRaster(int x, int y, int w, int h) {
        WritableRaster ret = createCompatibleWritableRaster(w, h);
        return ret.createWritableChild(0, 0, w, h, x, y, null);
    }
    
    public Raster createTranslatedChild(int childMinX, int childMinY) {
        return createChild(minX, minY, width, height, childMinX, childMinY, null);
    }
    
    public Raster createChild(int parentX, int parentY, int width, int height, int childMinX, int childMinY, int[] bandList) {
        if (parentX < this.minX) {
            throw new RasterFormatException("parentX lies outside raster");
        }
        if (parentY < this.minY) {
            throw new RasterFormatException("parentY lies outside raster");
        }
        if ((parentX + width < parentX) || (parentX + width > this.width + this.minX)) {
            throw new RasterFormatException("(parentX + width) is outside raster");
        }
        if ((parentY + height < parentY) || (parentY + height > this.height + this.minY)) {
            throw new RasterFormatException("(parentY + height) is outside raster");
        }
        SampleModel subSampleModel;
        if (bandList == null) {
            subSampleModel = sampleModel;
        } else {
            subSampleModel = sampleModel.createSubsetSampleModel(bandList);
        }
        int deltaX = childMinX - parentX;
        int deltaY = childMinY - parentY;
        return new Raster(subSampleModel, getDataBuffer(), new Rectangle(childMinX, childMinY, width, height), new Point(sampleModelTranslateX + deltaX, sampleModelTranslateY + deltaY), this);
    }
    
    public Rectangle getBounds() {
        return new Rectangle(minX, minY, width, height);
    }
    
    public final int getMinX() {
        return minX;
    }
    
    public final int getMinY() {
        return minY;
    }
    
    public final int getWidth() {
        return width;
    }
    
    public final int getHeight() {
        return height;
    }
    
    public final int getNumBands() {
        return numBands;
    }
    
    public final int getNumDataElements() {
        return sampleModel.getNumDataElements();
    }
    
    public final int getTransferType() {
        return sampleModel.getTransferType();
    }
    
    public DataBuffer getDataBuffer() {
        return dataBuffer;
    }
    
    public SampleModel getSampleModel() {
        return sampleModel;
    }
    
    public Object getDataElements(int x, int y, Object outData) {
        return sampleModel.getDataElements(x - sampleModelTranslateX, y - sampleModelTranslateY, outData, dataBuffer);
    }
    
    public Object getDataElements(int x, int y, int w, int h, Object outData) {
        return sampleModel.getDataElements(x - sampleModelTranslateX, y - sampleModelTranslateY, w, h, outData, dataBuffer);
    }
    
    public int[] getPixel(int x, int y, int[] iArray) {
        return sampleModel.getPixel(x - sampleModelTranslateX, y - sampleModelTranslateY, iArray, dataBuffer);
    }
    
    public float[] getPixel(int x, int y, float[] fArray) {
        return sampleModel.getPixel(x - sampleModelTranslateX, y - sampleModelTranslateY, fArray, dataBuffer);
    }
    
    public double[] getPixel(int x, int y, double[] dArray) {
        return sampleModel.getPixel(x - sampleModelTranslateX, y - sampleModelTranslateY, dArray, dataBuffer);
    }
    
    public int[] getPixels(int x, int y, int w, int h, int[] iArray) {
        return sampleModel.getPixels(x - sampleModelTranslateX, y - sampleModelTranslateY, w, h, iArray, dataBuffer);
    }
    
    public float[] getPixels(int x, int y, int w, int h, float[] fArray) {
        return sampleModel.getPixels(x - sampleModelTranslateX, y - sampleModelTranslateY, w, h, fArray, dataBuffer);
    }
    
    public double[] getPixels(int x, int y, int w, int h, double[] dArray) {
        return sampleModel.getPixels(x - sampleModelTranslateX, y - sampleModelTranslateY, w, h, dArray, dataBuffer);
    }
    
    public int getSample(int x, int y, int b) {
        return sampleModel.getSample(x - sampleModelTranslateX, y - sampleModelTranslateY, b, dataBuffer);
    }
    
    public float getSampleFloat(int x, int y, int b) {
        return sampleModel.getSampleFloat(x - sampleModelTranslateX, y - sampleModelTranslateY, b, dataBuffer);
    }
    
    public double getSampleDouble(int x, int y, int b) {
        return sampleModel.getSampleDouble(x - sampleModelTranslateX, y - sampleModelTranslateY, b, dataBuffer);
    }
    
    public int[] getSamples(int x, int y, int w, int h, int b, int[] iArray) {
        return sampleModel.getSamples(x - sampleModelTranslateX, y - sampleModelTranslateY, w, h, b, iArray, dataBuffer);
    }
    
    public float[] getSamples(int x, int y, int w, int h, int b, float[] fArray) {
        return sampleModel.getSamples(x - sampleModelTranslateX, y - sampleModelTranslateY, w, h, b, fArray, dataBuffer);
    }
    
    public double[] getSamples(int x, int y, int w, int h, int b, double[] dArray) {
        return sampleModel.getSamples(x - sampleModelTranslateX, y - sampleModelTranslateY, w, h, b, dArray, dataBuffer);
    }
}
