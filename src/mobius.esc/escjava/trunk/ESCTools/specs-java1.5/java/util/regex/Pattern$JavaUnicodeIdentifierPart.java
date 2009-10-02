package java.util.regex;

final class Pattern$JavaUnicodeIdentifierPart extends Pattern$JavaTypeClass {
    
    Pattern$JavaUnicodeIdentifierPart() {
        
    }
    
    boolean isProperty(int ch) {
        return Character.isUnicodeIdentifierPart(ch);
    }
}
