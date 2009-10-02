package java.util.regex;

final class Pattern$JavaLowerCase extends Pattern$JavaTypeClass {
    
    Pattern$JavaLowerCase() {
        
    }
    
    boolean isProperty(int ch) {
        return Character.isLowerCase(ch);
    }
}
