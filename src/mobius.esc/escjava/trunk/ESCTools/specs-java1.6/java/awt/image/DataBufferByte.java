package java.awt.image;

public final class DataBufferByte extends DataBuffer {
    byte[] data;
    byte[][] bankdata;
    
    public DataBufferByte(int size) {
        super(TYPE_BYTE, size);
        data = new byte[size];
        bankdata = new byte[1][];
        bankdata[0] = data;
    }
    
    public DataBufferByte(int size, int numBanks) {
        super(TYPE_BYTE, size, numBanks);
        bankdata = new byte[numBanks][];
        for (int i = 0; i < numBanks; i++) {
            bankdata[i] = new byte[size];
        }
        data = bankdata[0];
    }
    
    public DataBufferByte(byte[] dataArray, int size) {
        super(TYPE_BYTE, size);
        data = dataArray;
        bankdata = new byte[1][];
        bankdata[0] = data;
    }
    
    public DataBufferByte(byte[] dataArray, int size, int offset) {
        super(TYPE_BYTE, size, 1, offset);
        data = dataArray;
        bankdata = new byte[1][];
        bankdata[0] = data;
    }
    
    public DataBufferByte(byte[][] dataArray, int size) {
        super(TYPE_BYTE, size, dataArray.length);
        bankdata = (byte[][])(byte[][])dataArray.clone();
        data = bankdata[0];
    }
    
    public DataBufferByte(byte[][] dataArray, int size, int[] offsets) {
        super(TYPE_BYTE, size, dataArray.length, offsets);
        bankdata = (byte[][])(byte[][])dataArray.clone();
        data = bankdata[0];
    }
    
    public byte[] getData() {
        return data;
    }
    
    public byte[] getData(int bank) {
        return bankdata[bank];
    }
    
    public byte[][] getBankData() {
        return (byte[][])(byte[][])bankdata.clone();
    }
    
    public int getElem(int i) {
        return (int)(data[i + offset]) & 255;
    }
    
    public int getElem(int bank, int i) {
        return (int)(bankdata[bank][i + offsets[bank]]) & 255;
    }
    
    public void setElem(int i, int val) {
        data[i + offset] = (byte)val;
    }
    
    public void setElem(int bank, int i, int val) {
        bankdata[bank][i + offsets[bank]] = (byte)val;
    }
}
