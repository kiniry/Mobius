package java.util.regex;

final class Pattern$JavaIdentifierIgnorable extends Pattern$JavaTypeClass {
    
    Pattern$JavaIdentifierIgnorable() {
        
    }
    
    boolean isProperty(int ch) {
        return Character.isIdentifierIgnorable(ch);
    }
}
