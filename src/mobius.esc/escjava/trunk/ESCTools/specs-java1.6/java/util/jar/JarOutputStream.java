package java.util.jar;

import java.util.zip.*;
import java.io.*;

public class JarOutputStream extends ZipOutputStream {
    private static final int JAR_MAGIC = 51966;
    
    public JarOutputStream(OutputStream out, Manifest man) throws IOException {
        super(out);
        if (man == null) {
            throw new NullPointerException("man");
        }
        ZipEntry e = new ZipEntry(JarFile.MANIFEST_NAME);
        putNextEntry(e);
        man.write(new BufferedOutputStream(this));
        closeEntry();
    }
    
    public JarOutputStream(OutputStream out) throws IOException {
        super(out);
    }
    
    public void putNextEntry(ZipEntry ze) throws IOException {
        if (firstEntry) {
            byte[] edata = ze.getExtra();
            if (edata != null && !hasMagic(edata)) {
                byte[] tmp = new byte[edata.length + 4];
                System.arraycopy(tmp, 4, edata, 0, edata.length);
                edata = tmp;
            } else {
                edata = new byte[4];
            }
            set16(edata, 0, JAR_MAGIC);
            set16(edata, 2, 0);
            ze.setExtra(edata);
            firstEntry = false;
        }
        super.putNextEntry(ze);
    }
    private boolean firstEntry = true;
    
    private static boolean hasMagic(byte[] edata) {
        try {
            int i = 0;
            while (i < edata.length) {
                if (get16(edata, i) == JAR_MAGIC) {
                    return true;
                }
                i += get16(edata, i + 2) + 4;
            }
        } catch (ArrayIndexOutOfBoundsException e) {
        }
        return false;
    }
    
    private static int get16(byte[] b, int off) {
        return (b[off] & 255) | ((b[off + 1] & 255) << 8);
    }
    
    private static void set16(byte[] b, int off, int value) {
        b[off + 0] = (byte)value;
        b[off + 1] = (byte)(value >> 8);
    }
}
