package java.awt.image;

public final class DataBufferInt extends DataBuffer {
    int[] data;
    int[][] bankdata;
    
    public DataBufferInt(int size) {
        super(TYPE_INT, size);
        data = new int[size];
        bankdata = new int[1][];
        bankdata[0] = data;
    }
    
    public DataBufferInt(int size, int numBanks) {
        super(TYPE_INT, size, numBanks);
        bankdata = new int[numBanks][];
        for (int i = 0; i < numBanks; i++) {
            bankdata[i] = new int[size];
        }
        data = bankdata[0];
    }
    
    public DataBufferInt(int[] dataArray, int size) {
        super(TYPE_INT, size);
        data = dataArray;
        bankdata = new int[1][];
        bankdata[0] = data;
    }
    
    public DataBufferInt(int[] dataArray, int size, int offset) {
        super(TYPE_INT, size, 1, offset);
        data = dataArray;
        bankdata = new int[1][];
        bankdata[0] = data;
    }
    
    public DataBufferInt(int[][] dataArray, int size) {
        super(TYPE_INT, size, dataArray.length);
        bankdata = (int[][])(int[][])dataArray.clone();
        data = bankdata[0];
    }
    
    public DataBufferInt(int[][] dataArray, int size, int[] offsets) {
        super(TYPE_INT, size, dataArray.length, offsets);
        bankdata = (int[][])(int[][])dataArray.clone();
        data = bankdata[0];
    }
    
    public int[] getData() {
        return data;
    }
    
    public int[] getData(int bank) {
        return bankdata[bank];
    }
    
    public int[][] getBankData() {
        return (int[][])(int[][])bankdata.clone();
    }
    
    public int getElem(int i) {
        return data[i + offset];
    }
    
    public int getElem(int bank, int i) {
        return bankdata[bank][i + offsets[bank]];
    }
    
    public void setElem(int i, int val) {
        data[i + offset] = val;
    }
    
    public void setElem(int bank, int i, int val) {
        bankdata[bank][i + offsets[bank]] = (int)val;
    }
}
