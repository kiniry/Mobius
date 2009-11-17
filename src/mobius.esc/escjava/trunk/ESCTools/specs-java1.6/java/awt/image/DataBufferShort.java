package java.awt.image;

public final class DataBufferShort extends DataBuffer {
    short[] data;
    short[][] bankdata;
    
    public DataBufferShort(int size) {
        super(TYPE_SHORT, size);
        data = new short[size];
        bankdata = new short[1][];
        bankdata[0] = data;
    }
    
    public DataBufferShort(int size, int numBanks) {
        super(TYPE_SHORT, size, numBanks);
        bankdata = new short[numBanks][];
        for (int i = 0; i < numBanks; i++) {
            bankdata[i] = new short[size];
        }
        data = bankdata[0];
    }
    
    public DataBufferShort(short[] dataArray, int size) {
        super(TYPE_SHORT, size);
        data = dataArray;
        bankdata = new short[1][];
        bankdata[0] = data;
    }
    
    public DataBufferShort(short[] dataArray, int size, int offset) {
        super(TYPE_SHORT, size, 1, offset);
        data = dataArray;
        bankdata = new short[1][];
        bankdata[0] = data;
    }
    
    public DataBufferShort(short[][] dataArray, int size) {
        super(TYPE_SHORT, size, dataArray.length);
        bankdata = (short[][])(short[][])dataArray.clone();
        data = bankdata[0];
    }
    
    public DataBufferShort(short[][] dataArray, int size, int[] offsets) {
        super(TYPE_SHORT, size, dataArray.length, offsets);
        bankdata = (short[][])(short[][])dataArray.clone();
        data = bankdata[0];
    }
    
    public short[] getData() {
        return data;
    }
    
    public short[] getData(int bank) {
        return bankdata[bank];
    }
    
    public short[][] getBankData() {
        return (short[][])(short[][])bankdata.clone();
    }
    
    public int getElem(int i) {
        return (int)(data[i + offset]);
    }
    
    public int getElem(int bank, int i) {
        return (int)(bankdata[bank][i + offsets[bank]]);
    }
    
    public void setElem(int i, int val) {
        data[i + offset] = (short)val;
    }
    
    public void setElem(int bank, int i, int val) {
        bankdata[bank][i + offsets[bank]] = (short)val;
    }
}
