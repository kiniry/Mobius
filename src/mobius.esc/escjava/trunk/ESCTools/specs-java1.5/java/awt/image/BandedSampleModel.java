package java.awt.image;

public final class BandedSampleModel extends ComponentSampleModel {
    
    public BandedSampleModel(int dataType, int w, int h, int numBands) {
        super(dataType, w, h, 1, w, BandedSampleModel.createIndicesArray(numBands), BandedSampleModel.createOffsetArray(numBands));
    }
    
    public BandedSampleModel(int dataType, int w, int h, int scanlineStride, int[] bankIndices, int[] bandOffsets) {
        super(dataType, w, h, 1, scanlineStride, bankIndices, bandOffsets);
    }
    
    public SampleModel createCompatibleSampleModel(int w, int h) {
        int[] bandOffs;
        if (numBanks == 1) {
            bandOffs = orderBands(bandOffsets, w * h);
        } else {
            bandOffs = new int[bandOffsets.length];
        }
        SampleModel sampleModel = new BandedSampleModel(dataType, w, h, w, bankIndices, bandOffs);
        return sampleModel;
    }
    
    public SampleModel createSubsetSampleModel(int[] bands) {
        if (bands.length > bankIndices.length) throw new RasterFormatException("There are only " + bankIndices.length + " bands");
        int[] newBankIndices = new int[bands.length];
        int[] newBandOffsets = new int[bands.length];
        for (int i = 0; i < bands.length; i++) {
            newBankIndices[i] = bankIndices[bands[i]];
            newBandOffsets[i] = bandOffsets[bands[i]];
        }
        return new BandedSampleModel(this.dataType, width, height, this.scanlineStride, newBankIndices, newBandOffsets);
    }
    
    public DataBuffer createDataBuffer() {
        DataBuffer dataBuffer = null;
        int size = scanlineStride * height;
        switch (dataType) {
        case DataBuffer.TYPE_BYTE: 
            dataBuffer = new DataBufferByte(size, numBanks);
            break;
        
        case DataBuffer.TYPE_USHORT: 
            dataBuffer = new DataBufferUShort(size, numBanks);
            break;
        
        case DataBuffer.TYPE_SHORT: 
            dataBuffer = new DataBufferShort(size, numBanks);
            break;
        
        case DataBuffer.TYPE_INT: 
            dataBuffer = new DataBufferInt(size, numBanks);
            break;
        
        case DataBuffer.TYPE_FLOAT: 
            dataBuffer = new DataBufferFloat(size, numBanks);
            break;
        
        case DataBuffer.TYPE_DOUBLE: 
            dataBuffer = new DataBufferDouble(size, numBanks);
            break;
        
        default: 
            throw new IllegalArgumentException("dataType is not one of the supported types.");
        
        }
        return dataBuffer;
    }
    
    public Object getDataElements(int x, int y, Object obj, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x >= width) || (y >= height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        int type = getTransferType();
        int numDataElems = getNumDataElements();
        int pixelOffset = y * scanlineStride + x;
        switch (type) {
        case DataBuffer.TYPE_BYTE: 
            byte[] bdata;
            if (obj == null) {
                bdata = new byte[numDataElems];
            } else {
                bdata = (byte[])(byte[])obj;
            }
            for (int i = 0; i < numDataElems; i++) {
                bdata[i] = (byte)data.getElem(bankIndices[i], pixelOffset + bandOffsets[i]);
            }
            obj = (Object)bdata;
            break;
        
        case DataBuffer.TYPE_USHORT: 
        
        case DataBuffer.TYPE_SHORT: 
            short[] sdata;
            if (obj == null) {
                sdata = new short[numDataElems];
            } else {
                sdata = (short[])(short[])obj;
            }
            for (int i = 0; i < numDataElems; i++) {
                sdata[i] = (short)data.getElem(bankIndices[i], pixelOffset + bandOffsets[i]);
            }
            obj = (Object)sdata;
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] idata;
            if (obj == null) {
                idata = new int[numDataElems];
            } else {
                idata = (int[])(int[])obj;
            }
            for (int i = 0; i < numDataElems; i++) {
                idata[i] = data.getElem(bankIndices[i], pixelOffset + bandOffsets[i]);
            }
            obj = (Object)idata;
            break;
        
        case DataBuffer.TYPE_FLOAT: 
            float[] fdata;
            if (obj == null) {
                fdata = new float[numDataElems];
            } else {
                fdata = (float[])(float[])obj;
            }
            for (int i = 0; i < numDataElems; i++) {
                fdata[i] = data.getElemFloat(bankIndices[i], pixelOffset + bandOffsets[i]);
            }
            obj = (Object)fdata;
            break;
        
        case DataBuffer.TYPE_DOUBLE: 
            double[] ddata;
            if (obj == null) {
                ddata = new double[numDataElems];
            } else {
                ddata = (double[])(double[])obj;
            }
            for (int i = 0; i < numDataElems; i++) {
                ddata[i] = data.getElemDouble(bankIndices[i], pixelOffset + bandOffsets[i]);
            }
            obj = (Object)ddata;
            break;
        
        }
        return obj;
    }
    
    public int[] getPixel(int x, int y, int[] iArray, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x >= width) || (y >= height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        int[] pixels;
        if (iArray != null) {
            pixels = iArray;
        } else {
            pixels = new int[numBands];
        }
        int pixelOffset = y * scanlineStride + x;
        for (int i = 0; i < numBands; i++) {
            pixels[i] = data.getElem(bankIndices[i], pixelOffset + bandOffsets[i]);
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
        for (int k = 0; k < numBands; k++) {
            int lineOffset = y * scanlineStride + x + bandOffsets[k];
            int srcOffset = k;
            int bank = bankIndices[k];
            for (int i = 0; i < h; i++) {
                int pixelOffset = lineOffset;
                for (int j = 0; j < w; j++) {
                    pixels[srcOffset] = data.getElem(bank, pixelOffset++);
                    srcOffset += numBands;
                }
                lineOffset += scanlineStride;
            }
        }
        return pixels;
    }
    
    public int getSample(int x, int y, int b, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x >= width) || (y >= height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        int sample = data.getElem(bankIndices[b], y * scanlineStride + x + bandOffsets[b]);
        return sample;
    }
    
    public float getSampleFloat(int x, int y, int b, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x >= width) || (y >= height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        float sample = data.getElemFloat(bankIndices[b], y * scanlineStride + x + bandOffsets[b]);
        return sample;
    }
    
    public double getSampleDouble(int x, int y, int b, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x >= width) || (y >= height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        double sample = data.getElemDouble(bankIndices[b], y * scanlineStride + x + bandOffsets[b]);
        return sample;
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
        int lineOffset = y * scanlineStride + x + bandOffsets[b];
        int srcOffset = 0;
        int bank = bankIndices[b];
        for (int i = 0; i < h; i++) {
            int sampleOffset = lineOffset;
            for (int j = 0; j < w; j++) {
                samples[srcOffset++] = data.getElem(bank, sampleOffset++);
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
        int numDataElems = getNumDataElements();
        int pixelOffset = y * scanlineStride + x;
        switch (type) {
        case DataBuffer.TYPE_BYTE: 
            byte[] barray = (byte[])(byte[])obj;
            for (int i = 0; i < numDataElems; i++) {
                data.setElem(bankIndices[i], pixelOffset + bandOffsets[i], barray[i] & 255);
            }
            break;
        
        case DataBuffer.TYPE_USHORT: 
        
        case DataBuffer.TYPE_SHORT: 
            short[] sarray = (short[])(short[])obj;
            for (int i = 0; i < numDataElems; i++) {
                data.setElem(bankIndices[i], pixelOffset + bandOffsets[i], sarray[i] & 65535);
            }
            break;
        
        case DataBuffer.TYPE_INT: 
            int[] iarray = (int[])(int[])obj;
            for (int i = 0; i < numDataElems; i++) {
                data.setElem(bankIndices[i], pixelOffset + bandOffsets[i], iarray[i]);
            }
            break;
        
        case DataBuffer.TYPE_FLOAT: 
            float[] farray = (float[])(float[])obj;
            for (int i = 0; i < numDataElems; i++) {
                data.setElemFloat(bankIndices[i], pixelOffset + bandOffsets[i], farray[i]);
            }
            break;
        
        case DataBuffer.TYPE_DOUBLE: 
            double[] darray = (double[])(double[])obj;
            for (int i = 0; i < numDataElems; i++) {
                data.setElemDouble(bankIndices[i], pixelOffset + bandOffsets[i], darray[i]);
            }
            break;
        
        }
    }
    
    public void setPixel(int x, int y, int[] iArray, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x >= width) || (y >= height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        int pixelOffset = y * scanlineStride + x;
        for (int i = 0; i < numBands; i++) {
            data.setElem(bankIndices[i], pixelOffset + bandOffsets[i], iArray[i]);
        }
    }
    
    public void setPixels(int x, int y, int w, int h, int[] iArray, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x + w > width) || (y + h > height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        for (int k = 0; k < numBands; k++) {
            int lineOffset = y * scanlineStride + x + bandOffsets[k];
            int srcOffset = k;
            int bank = bankIndices[k];
            for (int i = 0; i < h; i++) {
                int pixelOffset = lineOffset;
                for (int j = 0; j < w; j++) {
                    data.setElem(bank, pixelOffset++, iArray[srcOffset]);
                    srcOffset += numBands;
                }
                lineOffset += scanlineStride;
            }
        }
    }
    
    public void setSample(int x, int y, int b, int s, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x >= width) || (y >= height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        data.setElem(bankIndices[b], y * scanlineStride + x + bandOffsets[b], s);
    }
    
    public void setSample(int x, int y, int b, float s, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x >= width) || (y >= height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        data.setElemFloat(bankIndices[b], y * scanlineStride + x + bandOffsets[b], s);
    }
    
    public void setSample(int x, int y, int b, double s, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x >= width) || (y >= height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        data.setElemDouble(bankIndices[b], y * scanlineStride + x + bandOffsets[b], s);
    }
    
    public void setSamples(int x, int y, int w, int h, int b, int[] iArray, DataBuffer data) {
        if ((x < 0) || (y < 0) || (x + w > width) || (y + h > height)) {
            throw new ArrayIndexOutOfBoundsException("Coordinate out of bounds!");
        }
        int lineOffset = y * scanlineStride + x + bandOffsets[b];
        int srcOffset = 0;
        int bank = bankIndices[b];
        for (int i = 0; i < h; i++) {
            int sampleOffset = lineOffset;
            for (int j = 0; j < w; j++) {
                data.setElem(bank, sampleOffset++, iArray[srcOffset++]);
            }
            lineOffset += scanlineStride;
        }
    }
    
    private static int[] createOffsetArray(int numBands) {
        int[] bandOffsets = new int[numBands];
        for (int i = 0; i < numBands; i++) {
            bandOffsets[i] = 0;
        }
        return bandOffsets;
    }
    
    private static int[] createIndicesArray(int numBands) {
        int[] bankIndices = new int[numBands];
        for (int i = 0; i < numBands; i++) {
            bankIndices[i] = i;
        }
        return bankIndices;
    }
    
    public int hashCode() {
        return super.hashCode() ^ 2;
    }
}
