package java.util.regex;

final class Pattern$JavaJavaIdentifierStart extends Pattern$JavaTypeClass {
    
    Pattern$JavaJavaIdentifierStart() {
        
    }
    
    boolean isProperty(int ch) {
        return Character.isJavaIdentifierStart(ch);
    }
}
