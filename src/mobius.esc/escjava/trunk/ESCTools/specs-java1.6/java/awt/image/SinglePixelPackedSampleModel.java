package java.awt.image;

import java.util.Arrays;

public class SinglePixelPackedSampleModel extends SampleModel {
    private int[] bitMasks;
    private int[] bitOffsets;
    private int[] bitSizes;
    private int maxBitSize;
    private int scanlineStride;
    
    private static native void initIDs();
    static {
        ColorModel.loadLibraries();
        initIDs();
    }
    
    public SinglePixelPackedSampleModel(int dataType, int w, int h, int[] bitMasks) {
        this(dataType, w, h, w, bitMasks);
        if (dataType != DataBuffer.TYPE_BYTE && dataType != DataBuffer.TYPE_USHORT && dataType != DataBuffer.TYPE_INT) {
            throw new IllegalArgumentException("Unsupported data type " + dataType);
        }
    }
    
    public SinglePixelPackedSampleModel(int dataType, int w, int h, int scanlineStride, int[] bitMasks) {
        super(dataType, w, h, bitMasks.length);
        if (dataType != DataBuffer.TYPE_BYTE && dataType != DataBuffer.TYPE_USHORT && dataType != DataBuffer.TYPE_INT) {
            throw new IllegalArgumentException("Unsupported data type " + dataType);
        }
        this.dataType = dataType;
        this.bitMasks = (int[])(int[])bitMasks.clone();
        this.scanlineStride = scanlineStride;
        this.bitOffsets = new int[numBands];
        this.bitSizes = new int[numBands];
        this.maxBitSize = 0;
        for (int i = 0; i < numBands; i++) {
            int bitOffset = 0;
            int bitSize = 0;
            int mask;
            mask = bitMasks[i];
            if (mask != 0) {
                while ((mask & 1) == 0) {
                    mask = mask >>> 1;
                    bitOffset++;
                }
                while ((mask & 1) == 1) {
                    mask = mask >>> 1;
                    bitSize++;
                }
                if (mask != 0) {
                    throw new IllegalArgumentException("Mask " + bitMasks[i] + " must be contiguous");
                }
            }
            bitOffsets[i] = bitOffset;
            bitSizes[i] = bitSize;
            if (bitSize > maxBitSize) {
                maxBitSize = bitSize;
            }
        }
    }
    
    public int getNumDataElements() {
        return 1;
    }
    
    private long getBufferSize() {
        long size = scanlineStride * (height - 1) + width;
        return size;
    }
    
    public SampleModel createCompatibleSampleModel(int w, int h) {
        SampleModel sampleModel = new SinglePixelPackedSampleModel(dataType, w, h, bitMasks);
        return sampleModel;
    }
    
    public DataBuffer createDataBuffer() {
        DataBuffer dataBuffer = null;
        int size = (int)getBufferSize();
        switch (dataType) {
        case DataBuffer.TYPE_BYTE: 
            dataBuffer = new DataBufferByte(size);
            break;
        
        case DataBuffer.TYPE_USHORT: 
            dataBuffer = new DataBufferUShort(size);
            break;
        
        case DataBuffer.TYPE_INT: 
            dataBuffer = new DataBufferInt(size);
            break;
        
        }
        return dataBuffer;
    }
    
    public int[] getSampleSize() {
        int mask;
        int[] sampleSize = new int[numBands];
        for (int i = 0; i < numBands; i++) {
            sampleSize[i] = 0;
            mask = bitMasks[i] >>> bitOffsets[i];
            while ((mask & 1) != 0) {
                sampleSize[i]++;
                mask = mask >>> 1;
            }
        }
        return sampleSize;
    }
    
    public int getSampleSize(int band) {
        int sampleSize = 0;
        int mask = bitMasks[band] >>> bitOffsets[band];
        while ((mask & 1) != 0) {
            sampleSize++;
            mask = mask >>> 1;
        }
        return sampleSize;
    }
    
    public int getOffset(int x, int y) {
        int offset = y * scanlineStride + x;
        return offset;
    }
    
    public int[] getBitOffsets() {
        return (int[])(int[])bitOffsets.clone();
    }
    
    public int[] getBitMasks() {
        return (int[])(int[])bitMasks.clone();
    }
    
    public int getScanlineStride() {
        return scanlineStride;
    }
    
    public SampleModel createSubsetSampleModel(int[] bands) {
        if (bands.length > numBands) throw new RasterFormatException("There are only " + numBands + " bands");
        int[] newBitMasks = new int[bands.length];
        for (int i = 0; i < bands.length; i++) newBitMasks[i] = bitMasks[bands[i]];
        return new SinglePixelPackedSampleModel(this.dataType, width, height, this.scanlineStride, newBitMasks);
    }
    
    public Object getDataElements(int x, int y, Object obj, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x >= width) || (y >= height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        int type = getTransferType();
        switch (type) {
        case DataBuffer.TYPE_BYTE: 
            byte[] bdata;
            if (obj == null) bdata = new byte[1]; else bdata = (byte[])(byte[])obj;
            bdata[0] = (byte)data.getElem(y * scanlineStride + x);
            obj = (Object)bdata;
            break;
        
        case DataBuffer.TYPE_USHORT: 
            short[] sdata;
            if (obj == null) sdata = new short[1]; else sdata = (short[])(short[])obj;
            sdata[0] = (short)data.getElem(y * scanlineStride + x);
            obj = (Object)sdata;
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] idata;
            if (obj == null) idata = new int[1]; else idata = (int[])(int[])obj;
            idata[0] = data.getElem(y * scanlineStride + x);
            obj = (Object)idata;
            break;
        
        }
        return obj;
    }
    
    public int[] getPixel(int x, int y, int[] iArray, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x >= width) || (y >= height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        int[] pixels;
        if (iArray == null) {
            pixels = new int[numBands];
        } else {
            pixels = iArray;
        }
        int value = data.getElem(y * scanlineStride + x);
        for (int i = 0; i < numBands; i++) {
            pixels[i] = (value & bitMasks[i]) >>> bitOffsets[i];
        }
        return pixels;
    }
    
    public int[] getPixels(int x, int y, int w, int h, int[] iArray, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x + w > width) || (y + h > height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        int[] pixels;
        if (iArray != null) {
            pixels = iArray;
        } else {
            pixels = new int[w * h * numBands];
        }
        int lineOffset = y * scanlineStride + x;
        int dstOffset = 0;
        for (int i = 0; i < h; i++) {
            for (int j = 0; j < w; j++) {
                int value = data.getElem(lineOffset + j);
                for (int k = 0; k < numBands; k++) {
                    pixels[dstOffset++] = ((value & bitMasks[k]) >>> bitOffsets[k]);
                }
            }
            lineOffset += scanlineStride;
        }
        return pixels;
    }
    
    public int getSample(int x, int y, int b, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x >= width) || (y >= height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        int sample = data.getElem(y * scanlineStride + x);
        return ((sample & bitMasks[b]) >>> bitOffsets[b]);
    }
    
    public int[] getSamples(int x, int y, int w, int h, int b, int[] iArray, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x + w > width) || (y + h > height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        int[] samples;
        if (iArray != null) {
            samples = iArray;
        } else {
            samples = new int[w * h];
        }
        int lineOffset = y * scanlineStride + x;
        int dstOffset = 0;
        for (int i = 0; i < h; i++) {
            for (int j = 0; j < w; j++) {
                int value = data.getElem(lineOffset + j);
                samples[dstOffset++] = ((value & bitMasks[b]) >>> bitOffsets[b]);
            }
            lineOffset += scanlineStride;
        }
        return samples;
    }
    
    public void setDataElements(int x, int y, Object obj, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x >= width) || (y >= height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        int type = getTransferType();
        switch (type) {
        case DataBuffer.TYPE_BYTE: 
            byte[] barray = (byte[])(byte[])obj;
            data.setElem(y * scanlineStride + x, ((int)barray[0]) & 255);
            break;
        
        case DataBuffer.TYPE_USHORT: 
            short[] sarray = (short[])(short[])obj;
            data.setElem(y * scanlineStride + x, ((int)sarray[0]) & 65535);
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] iarray = (int[])(int[])obj;
            data.setElem(y * scanlineStride + x, iarray[0]);
            break;
        
        }
    }
    
    public void setPixel(int x, int y, int[] iArray, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x >= width) || (y >= height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        int lineOffset = y * scanlineStride + x;
        int value = data.getElem(lineOffset);
        for (int i = 0; i < numBands; i++) {
            value &= ~bitMasks[i];
            value |= ((iArray[i] << bitOffsets[i]) & bitMasks[i]);
        }
        data.setElem(lineOffset, value);
    }
    
    public void setPixels(int x, int y, int w, int h, int[] iArray, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x + w > width) || (y + h > height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        int lineOffset = y * scanlineStride + x;
        int srcOffset = 0;
        for (int i = 0; i < h; i++) {
            for (int j = 0; j < w; j++) {
                int value = data.getElem(lineOffset + j);
                for (int k = 0; k < numBands; k++) {
                    value &= ~bitMasks[k];
                    int srcValue = iArray[srcOffset++];
                    value |= ((srcValue << bitOffsets[k]) & bitMasks[k]);
                }
                data.setElem(lineOffset + j, value);
            }
            lineOffset += scanlineStride;
        }
    }
    
    public void setSample(int x, int y, int b, int s, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x >= width) || (y >= height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        int value = data.getElem(y * scanlineStride + x);
        value &= ~bitMasks[b];
        value |= (s << bitOffsets[b]) & bitMasks[b];
        data.setElem(y * scanlineStride + x, value);
    }
    
    public void setSamples(int x, int y, int w, int h, int b, int[] iArray, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x + w > width) || (y + h > height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        int lineOffset = y * scanlineStride + x;
        int srcOffset = 0;
        for (int i = 0; i < h; i++) {
            for (int j = 0; j < w; j++) {
                int value = data.getElem(lineOffset + j);
                value &= ~bitMasks[b];
                int sample = iArray[srcOffset++];
                value |= ((int)sample << bitOffsets[b]) & bitMasks[b];
                data.setElem(lineOffset + j, value);
            }
            lineOffset += scanlineStride;
        }
    }
    
    public boolean equals(Object o) {
        if ((o == null) || !(o instanceof SinglePixelPackedSampleModel)) {
            return false;
        }
        SinglePixelPackedSampleModel that = (SinglePixelPackedSampleModel)(SinglePixelPackedSampleModel)o;
        return this.width == that.width && this.height == that.height && this.numBands == that.numBands && this.dataType == that.dataType && Arrays.equals(this.bitMasks, that.bitMasks) && Arrays.equals(this.bitOffsets, that.bitOffsets) && Arrays.equals(this.bitSizes, that.bitSizes) && this.maxBitSize == that.maxBitSize && this.scanlineStride == that.scanlineStride;
    }
    
    public int hashCode() {
        int hash = 0;
        hash = width;
        hash <<= 8;
        hash ^= height;
        hash <<= 8;
        hash ^= numBands;
        hash <<= 8;
        hash ^= dataType;
        hash <<= 8;
        for (int i = 0; i < bitMasks.length; i++) {
            hash ^= bitMasks[i];
            hash <<= 8;
        }
        for (int i = 0; i < bitOffsets.length; i++) {
            hash ^= bitOffsets[i];
            hash <<= 8;
        }
        for (int i = 0; i < bitSizes.length; i++) {
            hash ^= bitSizes[i];
            hash <<= 8;
        }
        hash ^= maxBitSize;
        hash <<= 8;
        hash ^= scanlineStride;
        return hash;
    }
}
