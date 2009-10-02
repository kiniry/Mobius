package java.util.regex;

final class Pattern$JavaLetterOrDigit extends Pattern$JavaTypeClass {
    
    Pattern$JavaLetterOrDigit() {
        
    }
    
    boolean isProperty(int ch) {
        return Character.isLetterOrDigit(ch);
    }
}
