package java.util.regex;

final class Pattern$JavaUnicodeIdentifierStart extends Pattern$JavaTypeClass {
    
    Pattern$JavaUnicodeIdentifierStart() {
        
    }
    
    boolean isProperty(int ch) {
        return Character.isUnicodeIdentifierStart(ch);
    }
}
