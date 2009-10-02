package java.util.regex;

final class Pattern$JavaWhitespace extends Pattern$JavaTypeClass {
    
    Pattern$JavaWhitespace() {
        
    }
    
    boolean isProperty(int ch) {
        return Character.isWhitespace(ch);
    }
}
