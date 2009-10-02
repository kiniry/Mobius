package java.util.regex;

final class Pattern$JavaSpaceChar extends Pattern$JavaTypeClass {
    
    Pattern$JavaSpaceChar() {
        
    }
    
    boolean isProperty(int ch) {
        return Character.isSpaceChar(ch);
    }
}
