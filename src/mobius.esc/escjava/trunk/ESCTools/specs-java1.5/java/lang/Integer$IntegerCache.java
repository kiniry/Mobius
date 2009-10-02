package java.lang;

class Integer$IntegerCache {
    
    private Integer$IntegerCache() {
        
    }
    static final Integer[] cache = new Integer[-(-128) + 127 + 1];
    static {
        for (int i = 0; i < cache.length; i++) cache[i] = new Integer(i - 128);
    }
}
