package java.util.regex;

final class Pattern$JavaDigit extends Pattern$JavaTypeClass {
    
    Pattern$JavaDigit() {
        
    }
    
    boolean isProperty(int ch) {
        return Character.isDigit(ch);
    }
}
