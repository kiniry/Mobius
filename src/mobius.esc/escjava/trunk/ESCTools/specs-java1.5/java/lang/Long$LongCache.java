package java.lang;

class Long$LongCache {
    
    private Long$LongCache() {
        
    }
    static final Long[] cache = new Long[-(-128) + 127 + 1];
    static {
        for (int i = 0; i < cache.length; i++) cache[i] = new Long(i - 128);
    }
}
