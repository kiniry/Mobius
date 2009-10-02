package java.util.regex;

final class Pattern$JavaTitleCase extends Pattern$JavaTypeClass {
    
    Pattern$JavaTitleCase() {
        
    }
    
    boolean isProperty(int ch) {
        return Character.isTitleCase(ch);
    }
}
