package java.lang;

class Short$ShortCache {
    
    private Short$ShortCache() {
        
    }
    static final Short[] cache = new Short[-(-128) + 127 + 1];
    static {
        for (int i = 0; i < cache.length; i++) cache[i] = new Short((short)(i - 128));
    }
}
