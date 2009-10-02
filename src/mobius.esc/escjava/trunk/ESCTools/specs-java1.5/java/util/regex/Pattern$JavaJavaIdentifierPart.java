package java.util.regex;

final class Pattern$JavaJavaIdentifierPart extends Pattern$JavaTypeClass {
    
    Pattern$JavaJavaIdentifierPart() {
        
    }
    
    boolean isProperty(int ch) {
        return Character.isJavaIdentifierPart(ch);
    }
}
