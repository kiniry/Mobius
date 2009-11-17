package java.awt.image;

public abstract class DataBuffer {
    public static final int TYPE_BYTE = 0;
    public static final int TYPE_USHORT = 1;
    public static final int TYPE_SHORT = 2;
    public static final int TYPE_INT = 3;
    public static final int TYPE_FLOAT = 4;
    public static final int TYPE_DOUBLE = 5;
    public static final int TYPE_UNDEFINED = 32;
    protected int dataType;
    protected int banks;
    protected int offset;
    protected int size;
    protected int[] offsets;
    private static final int[] dataTypeSize = {8, 16, 16, 32, 32, 64};
    
    public static int getDataTypeSize(int type) {
        if (type < TYPE_BYTE || type > TYPE_DOUBLE) {
            throw new IllegalArgumentException("Unknown data type " + type);
        }
        return dataTypeSize[type];
    }
    
    protected DataBuffer(int dataType, int size) {
        
        this.dataType = dataType;
        this.banks = 1;
        this.size = size;
        this.offset = 0;
        this.offsets = new int[1];
    }
    
    protected DataBuffer(int dataType, int size, int numBanks) {
        
        this.dataType = dataType;
        this.banks = numBanks;
        this.size = size;
        this.offset = 0;
        this.offsets = new int[banks];
    }
    
    protected DataBuffer(int dataType, int size, int numBanks, int offset) {
        
        this.dataType = dataType;
        this.banks = numBanks;
        this.size = size;
        this.offset = offset;
        this.offsets = new int[numBanks];
        for (int i = 0; i < numBanks; i++) {
            this.offsets[i] = offset;
        }
    }
    
    protected DataBuffer(int dataType, int size, int numBanks, int[] offsets) {
        
        if (numBanks != offsets.length) {
            throw new ArrayIndexOutOfBoundsException("Number of banks does not match number of bank offsets");
        }
        this.dataType = dataType;
        this.banks = numBanks;
        this.size = size;
        this.offset = offsets[0];
        this.offsets = (int[])(int[])offsets.clone();
    }
    
    public int getDataType() {
        return dataType;
    }
    
    public int getSize() {
        return size;
    }
    
    public int getOffset() {
        return offset;
    }
    
    public int[] getOffsets() {
        return (int[])(int[])offsets.clone();
    }
    
    public int getNumBanks() {
        return banks;
    }
    
    public int getElem(int i) {
        return getElem(0, i);
    }
    
    public abstract int getElem(int bank, int i);
    
    public void setElem(int i, int val) {
        setElem(0, i, val);
    }
    
    public abstract void setElem(int bank, int i, int val);
    
    public float getElemFloat(int i) {
        return (float)getElem(i);
    }
    
    public float getElemFloat(int bank, int i) {
        return (float)getElem(bank, i);
    }
    
    public void setElemFloat(int i, float val) {
        setElem(i, (int)val);
    }
    
    public void setElemFloat(int bank, int i, float val) {
        setElem(bank, i, (int)val);
    }
    
    public double getElemDouble(int i) {
        return (double)getElem(i);
    }
    
    public double getElemDouble(int bank, int i) {
        return (double)getElem(bank, i);
    }
    
    public void setElemDouble(int i, double val) {
        setElem(i, (int)val);
    }
    
    public void setElemDouble(int bank, int i, double val) {
        setElem(bank, i, (int)val);
    }
    
    static int[] toIntArray(Object obj) {
        if (obj instanceof int[]) {
            return (int[])(int[])obj;
        } else if (obj == null) {
            return null;
        } else if (obj instanceof short[]) {
            short[] sdata = (short[])(short[])obj;
            int[] idata = new int[sdata.length];
            for (int i = 0; i < sdata.length; i++) {
                idata[i] = (int)sdata[i] & 65535;
            }
            return idata;
        } else if (obj instanceof byte[]) {
            byte[] bdata = (byte[])(byte[])obj;
            int[] idata = new int[bdata.length];
            for (int i = 0; i < bdata.length; i++) {
                idata[i] = 255 & (int)bdata[i];
            }
            return idata;
        }
        return null;
    }
}
