package java.io;

public class DataOutputStream extends FilterOutputStream implements DataOutput {
    protected int written;
    private byte[] bytearr = null;
    
    public DataOutputStream(OutputStream out) {
        super(out);
    }
    
    private void incCount(int value) {
        int temp = written + value;
        if (temp < 0) {
            temp = Integer.MAX_VALUE;
        }
        written = temp;
    }
    
    public synchronized void write(int b) throws IOException {
        out.write(b);
        incCount(1);
    }
    
    public synchronized void write(byte[] b, int off, int len) throws IOException {
        out.write(b, off, len);
        incCount(len);
    }
    
    public void flush() throws IOException {
        out.flush();
    }
    
    public final void writeBoolean(boolean v) throws IOException {
        out.write(v ? 1 : 0);
        incCount(1);
    }
    
    public final void writeByte(int v) throws IOException {
        out.write(v);
        incCount(1);
    }
    
    public final void writeShort(int v) throws IOException {
        out.write((v >>> 8) & 255);
        out.write((v >>> 0) & 255);
        incCount(2);
    }
    
    public final void writeChar(int v) throws IOException {
        out.write((v >>> 8) & 255);
        out.write((v >>> 0) & 255);
        incCount(2);
    }
    
    public final void writeInt(int v) throws IOException {
        out.write((v >>> 24) & 255);
        out.write((v >>> 16) & 255);
        out.write((v >>> 8) & 255);
        out.write((v >>> 0) & 255);
        incCount(4);
    }
    private byte[] writeBuffer = new byte[8];
    
    public final void writeLong(long v) throws IOException {
        writeBuffer[0] = (byte)(v >>> 56);
        writeBuffer[1] = (byte)(v >>> 48);
        writeBuffer[2] = (byte)(v >>> 40);
        writeBuffer[3] = (byte)(v >>> 32);
        writeBuffer[4] = (byte)(v >>> 24);
        writeBuffer[5] = (byte)(v >>> 16);
        writeBuffer[6] = (byte)(v >>> 8);
        writeBuffer[7] = (byte)(v >>> 0);
        out.write(writeBuffer, 0, 8);
        incCount(8);
    }
    
    public final void writeFloat(float v) throws IOException {
        writeInt(Float.floatToIntBits(v));
    }
    
    public final void writeDouble(double v) throws IOException {
        writeLong(Double.doubleToLongBits(v));
    }
    
    public final void writeBytes(String s) throws IOException {
        int len = s.length();
        for (int i = 0; i < len; i++) {
            out.write((byte)s.charAt(i));
        }
        incCount(len);
    }
    
    public final void writeChars(String s) throws IOException {
        int len = s.length();
        for (int i = 0; i < len; i++) {
            int v = s.charAt(i);
            out.write((v >>> 8) & 255);
            out.write((v >>> 0) & 255);
        }
        incCount(len * 2);
    }
    
    public final void writeUTF(String str) throws IOException {
        writeUTF(str, this);
    }
    
    static int writeUTF(String str, DataOutput out) throws IOException {
        int strlen = str.length();
        int utflen = 0;
        int c;
        int count = 0;
        for (int i = 0; i < strlen; i++) {
            c = str.charAt(i);
            if ((c >= 1) && (c <= 127)) {
                utflen++;
            } else if (c > 2047) {
                utflen += 3;
            } else {
                utflen += 2;
            }
        }
        if (utflen > 65535) throw new UTFDataFormatException("encoded string too long: " + utflen + " bytes");
        byte[] bytearr = null;
        if (out instanceof DataOutputStream) {
            DataOutputStream dos = (DataOutputStream)(DataOutputStream)out;
            if (dos.bytearr == null || (dos.bytearr.length < (utflen + 2))) dos.bytearr = new byte[(utflen * 2) + 2];
            bytearr = dos.bytearr;
        } else {
            bytearr = new byte[utflen + 2];
        }
        bytearr[count++] = (byte)((utflen >>> 8) & 255);
        bytearr[count++] = (byte)((utflen >>> 0) & 255);
        int i = 0;
        for (i = 0; i < strlen; i++) {
            c = str.charAt(i);
            if (!((c >= 1) && (c <= 127))) break;
            bytearr[count++] = (byte)c;
        }
        for (; i < strlen; i++) {
            c = str.charAt(i);
            if ((c >= 1) && (c <= 127)) {
                bytearr[count++] = (byte)c;
            } else if (c > 2047) {
                bytearr[count++] = (byte)(224 | ((c >> 12) & 15));
                bytearr[count++] = (byte)(128 | ((c >> 6) & 63));
                bytearr[count++] = (byte)(128 | ((c >> 0) & 63));
            } else {
                bytearr[count++] = (byte)(192 | ((c >> 6) & 31));
                bytearr[count++] = (byte)(128 | ((c >> 0) & 63));
            }
        }
        out.write(bytearr, 0, utflen + 2);
        return utflen + 2;
    }
    
    public final int size() {
        return written;
    }
}
