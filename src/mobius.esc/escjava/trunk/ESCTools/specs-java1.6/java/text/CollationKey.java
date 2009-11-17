package java.text;

public final class CollationKey implements Comparable {
    
    public int compareTo(CollationKey target) {
        int result = key.compareTo(target.key);
        if (result <= Collator.LESS) return Collator.LESS; else if (result >= Collator.GREATER) return Collator.GREATER;
        return Collator.EQUAL;
    }
    
    public boolean equals(Object target) {
        if (this == target) return true;
        if (target == null || !getClass().equals(target.getClass())) {
            return false;
        }
        CollationKey other = (CollationKey)(CollationKey)target;
        return key.equals(other.key);
    }
    
    public int hashCode() {
        return (key.hashCode());
    }
    
    public String getSourceString() {
        return source;
    }
    
    public byte[] toByteArray() {
        char[] src = key.toCharArray();
        byte[] dest = new byte[2 * src.length];
        int j = 0;
        for (int i = 0; i < src.length; i++) {
            dest[j++] = (byte)(src[i] >>> 8);
            dest[j++] = (byte)(src[i] & 255);
        }
        return dest;
    }
    
    CollationKey(String source, String key) {
        
        this.source = source;
        this.key = key;
    }
    private String source = null;
    private String key = null;
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((CollationKey)x0);
    }
}
