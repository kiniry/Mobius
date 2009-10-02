package java.awt.image;

public class ByteLookupTable extends LookupTable {
    byte[][] data;
    
    public ByteLookupTable(int offset, byte[][] data) {
        super(offset, data.length);
        numComponents = data.length;
        numEntries = data[0].length;
        this.data = new byte[numComponents][];
        for (int i = 0; i < numComponents; i++) {
            this.data[i] = data[i];
        }
    }
    
    public ByteLookupTable(int offset, byte[] data) {
        super(offset, data.length);
        numComponents = 1;
        numEntries = data.length;
        this.data = new byte[1][];
        this.data[0] = data;
    }
    
    public final byte[][] getTable() {
        return data;
    }
    
    public int[] lookupPixel(int[] src, int[] dst) {
        if (dst == null) {
            dst = new int[src.length];
        }
        if (numComponents == 1) {
            for (int i = 0; i < src.length; i++) {
                int s = src[i] - offset;
                if (s < 0) {
                    throw new ArrayIndexOutOfBoundsException("src[" + i + "]-offset is " + "less than zero");
                }
                dst[i] = (int)data[0][s];
            }
        } else {
            for (int i = 0; i < src.length; i++) {
                int s = src[i] - offset;
                if (s < 0) {
                    throw new ArrayIndexOutOfBoundsException("src[" + i + "]-offset is " + "less than zero");
                }
                dst[i] = (int)data[i][s];
            }
        }
        return dst;
    }
    
    public byte[] lookupPixel(byte[] src, byte[] dst) {
        if (dst == null) {
            dst = new byte[src.length];
        }
        if (numComponents == 1) {
            for (int i = 0; i < src.length; i++) {
                int s = (src[i] & 255) - offset;
                if (s < 0) {
                    throw new ArrayIndexOutOfBoundsException("src[" + i + "]-offset is " + "less than zero");
                }
                dst[i] = data[0][s];
            }
        } else {
            for (int i = 0; i < src.length; i++) {
                int s = (src[i] & 255) - offset;
                if (s < 0) {
                    throw new ArrayIndexOutOfBoundsException("src[" + i + "]-offset is " + "less than zero");
                }
                dst[i] = data[i][s];
            }
        }
        return dst;
    }
}
