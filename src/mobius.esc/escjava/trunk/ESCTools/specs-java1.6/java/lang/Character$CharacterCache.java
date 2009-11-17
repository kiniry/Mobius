package java.lang;

class Character$CharacterCache {
    
    private Character$CharacterCache() {
        
    }
    static final Character[] cache = new Character[127 + 1];
    static {
        for (int i = 0; i < cache.length; i++) cache[i] = new Character((char)i);
    }
}
