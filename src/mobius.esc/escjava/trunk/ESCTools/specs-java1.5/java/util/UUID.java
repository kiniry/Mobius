package java.util;

import java.security.*;

public final class UUID implements java.io.Serializable, Comparable {
    /*synthetic*/ static final boolean $assertionsDisabled = !UUID.class.desiredAssertionStatus();
    private static final long serialVersionUID = -4856846361193249489L;
    private final long mostSigBits;
    private final long leastSigBits;
    private transient int version = -1;
    private transient int variant = -1;
    private volatile transient long timestamp = -1;
    private transient int sequence = -1;
    private transient long node = -1;
    private transient int hashCode = -1;
    private static volatile SecureRandom numberGenerator = null;
    
    private UUID(byte[] data) {
        
        long msb = 0;
        long lsb = 0;
        if (!$assertionsDisabled && !(data.length == 16)) throw new AssertionError();
        for (int i = 0; i < 8; i++) msb = (msb << 8) | (data[i] & 255);
        for (int i = 8; i < 16; i++) lsb = (lsb << 8) | (data[i] & 255);
        this.mostSigBits = msb;
        this.leastSigBits = lsb;
    }
    
    public UUID(long mostSigBits, long leastSigBits) {
        
        this.mostSigBits = mostSigBits;
        this.leastSigBits = leastSigBits;
    }
    
    public static UUID randomUUID() {
        SecureRandom ng = numberGenerator;
        if (ng == null) {
            numberGenerator = ng = new SecureRandom();
        }
        byte[] randomBytes = new byte[16];
        ng.nextBytes(randomBytes);
        randomBytes[6] &= 15;
        randomBytes[6] |= 64;
        randomBytes[8] &= 63;
        randomBytes[8] |= 128;
        UUID result = new UUID(randomBytes);
        return new UUID(randomBytes);
    }
    
    public static UUID nameUUIDFromBytes(byte[] name) {
        MessageDigest md;
        try {
            md = MessageDigest.getInstance("MD5");
        } catch (NoSuchAlgorithmException nsae) {
            throw new InternalError("MD5 not supported");
        }
        byte[] md5Bytes = md.digest(name);
        md5Bytes[6] &= 15;
        md5Bytes[6] |= 48;
        md5Bytes[8] &= 63;
        md5Bytes[8] |= 128;
        return new UUID(md5Bytes);
    }
    
    public static UUID fromString(String name) {
        String[] components = name.split("-");
        if (components.length != 5) throw new IllegalArgumentException("Invalid UUID string: " + name);
        for (int i = 0; i < 5; i++) components[i] = "0x" + components[i];
        long mostSigBits = Long.decode(components[0]).longValue();
        mostSigBits <<= 16;
        mostSigBits |= Long.decode(components[1]).longValue();
        mostSigBits <<= 16;
        mostSigBits |= Long.decode(components[2]).longValue();
        long leastSigBits = Long.decode(components[3]).longValue();
        leastSigBits <<= 48;
        leastSigBits |= Long.decode(components[4]).longValue();
        return new UUID(mostSigBits, leastSigBits);
    }
    
    public long getLeastSignificantBits() {
        return leastSigBits;
    }
    
    public long getMostSignificantBits() {
        return mostSigBits;
    }
    
    public int version() {
        if (version < 0) {
            version = (int)((mostSigBits >> 12) & 15);
        }
        return version;
    }
    
    public int variant() {
        if (variant < 0) {
            if ((leastSigBits >>> 63) == 0) {
                variant = 0;
            } else if ((leastSigBits >>> 62) == 2) {
                variant = 2;
            } else {
                variant = (int)(leastSigBits >>> 61);
            }
        }
        return variant;
    }
    
    public long timestamp() {
        if (version() != 1) {
            throw new UnsupportedOperationException("Not a time-based UUID");
        }
        long result = timestamp;
        if (result < 0) {
            result = (mostSigBits & 4095L) << 48;
            result |= ((mostSigBits >> 16) & 65535L) << 32;
            result |= mostSigBits >>> 32;
            timestamp = result;
        }
        return result;
    }
    
    public int clockSequence() {
        if (version() != 1) {
            throw new UnsupportedOperationException("Not a time-based UUID");
        }
        if (sequence < 0) {
            sequence = (int)((leastSigBits & 4611404543450677248L) >>> 48);
        }
        return sequence;
    }
    
    public long node() {
        if (version() != 1) {
            throw new UnsupportedOperationException("Not a time-based UUID");
        }
        if (node < 0) {
            node = leastSigBits & 281474976710655L;
        }
        return node;
    }
    
    public String toString() {
        return (digits(mostSigBits >> 32, 8) + "-" + digits(mostSigBits >> 16, 4) + "-" + digits(mostSigBits, 4) + "-" + digits(leastSigBits >> 48, 4) + "-" + digits(leastSigBits, 12));
    }
    
    private static String digits(long val, int digits) {
        long hi = 1L << (digits * 4);
        return Long.toHexString(hi | (val & (hi - 1))).substring(1);
    }
    
    public int hashCode() {
        if (hashCode == -1) {
            hashCode = (int)((mostSigBits >> 32) ^ mostSigBits ^ (leastSigBits >> 32) ^ leastSigBits);
        }
        return hashCode;
    }
    
    public boolean equals(Object obj) {
        if (!(obj instanceof UUID)) return false;
        if (((UUID)(UUID)obj).variant() != this.variant()) return false;
        UUID id = (UUID)(UUID)obj;
        return (mostSigBits == id.mostSigBits && leastSigBits == id.leastSigBits);
    }
    
    public int compareTo(UUID val) {
        return (this.mostSigBits < val.mostSigBits ? -1 : (this.mostSigBits > val.mostSigBits ? 1 : (this.leastSigBits < val.leastSigBits ? -1 : (this.leastSigBits > val.leastSigBits ? 1 : 0))));
    }
    
    private void readObject(java.io.ObjectInputStream in) throws java.io.IOException, ClassNotFoundException {
        in.defaultReadObject();
        version = -1;
        variant = -1;
        timestamp = -1;
        sequence = -1;
        node = -1;
        hashCode = -1;
    }
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((UUID)x0);
    }
}
