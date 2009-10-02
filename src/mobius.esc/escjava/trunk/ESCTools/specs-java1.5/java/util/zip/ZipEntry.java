package java.util.zip;

import java.util.Date;

public class ZipEntry implements ZipConstants, Cloneable {
    String name;
    long time = -1;
    long crc = -1;
    long size = -1;
    long csize = -1;
    int method = -1;
    byte[] extra;
    String comment;
    int flag;
    int version;
    long offset;
    public static final int STORED = 0;
    public static final int DEFLATED = 8;
    static {
        initIDs();
    }
    
    private static native void initIDs();
    
    public ZipEntry(String name) {
        
        if (name == null) {
            throw new NullPointerException();
        }
        if (name.length() > 65535) {
            throw new IllegalArgumentException("entry name too long");
        }
        this.name = name;
    }
    
    public ZipEntry(ZipEntry e) {
        
        name = e.name;
        time = e.time;
        crc = e.crc;
        size = e.size;
        csize = e.csize;
        method = e.method;
        extra = e.extra;
        comment = e.comment;
    }
    
    ZipEntry(String name, long jzentry) {
        
        this.name = name;
        initFields(jzentry);
    }
    
    private native void initFields(long jzentry);
    
    ZipEntry(long jzentry) {
        
        initFields(jzentry);
    }
    
    public String getName() {
        return name;
    }
    
    public void setTime(long time) {
        this.time = javaToDosTime(time);
    }
    
    public long getTime() {
        return time != -1 ? dosToJavaTime(time) : -1;
    }
    
    public void setSize(long size) {
        if (size < 0 || size > 4294967295L) {
            throw new IllegalArgumentException("invalid entry size");
        }
        this.size = size;
    }
    
    public long getSize() {
        return size;
    }
    
    public long getCompressedSize() {
        return csize;
    }
    
    public void setCompressedSize(long csize) {
        this.csize = csize;
    }
    
    public void setCrc(long crc) {
        if (crc < 0 || crc > 4294967295L) {
            throw new IllegalArgumentException("invalid entry crc-32");
        }
        this.crc = crc;
    }
    
    public long getCrc() {
        return crc;
    }
    
    public void setMethod(int method) {
        if (method != STORED && method != DEFLATED) {
            throw new IllegalArgumentException("invalid compression method");
        }
        this.method = method;
    }
    
    public int getMethod() {
        return method;
    }
    
    public void setExtra(byte[] extra) {
        if (extra != null && extra.length > 65535) {
            throw new IllegalArgumentException("invalid extra field length");
        }
        this.extra = extra;
    }
    
    public byte[] getExtra() {
        return extra;
    }
    
    public void setComment(String comment) {
        if (comment != null && comment.length() > 65535 / 3 && ZipOutputStream.getUTF8Length(comment) > 65535) {
            throw new IllegalArgumentException("invalid entry comment length");
        }
        this.comment = comment;
    }
    
    public String getComment() {
        return comment;
    }
    
    public boolean isDirectory() {
        return name.endsWith("/");
    }
    
    public String toString() {
        return getName();
    }
    
    private static long dosToJavaTime(long dtime) {
        Date d = new Date((int)(((dtime >> 25) & 127) + 80), (int)(((dtime >> 21) & 15) - 1), (int)((dtime >> 16) & 31), (int)((dtime >> 11) & 31), (int)((dtime >> 5) & 63), (int)((dtime << 1) & 62));
        return d.getTime();
    }
    
    private static long javaToDosTime(long time) {
        Date d = new Date(time);
        int year = d.getYear() + 1900;
        if (year < 1980) {
            return (1 << 21) | (1 << 16);
        }
        return (year - 1980) << 25 | (d.getMonth() + 1) << 21 | d.getDate() << 16 | d.getHours() << 11 | d.getMinutes() << 5 | d.getSeconds() >> 1;
    }
    
    public int hashCode() {
        return name.hashCode();
    }
    
    public Object clone() {
        try {
            ZipEntry e = (ZipEntry)(ZipEntry)super.clone();
            e.extra = (extra == null ? null : (byte[])(byte[])extra.clone());
            return e;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
}
