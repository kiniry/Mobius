package java.util.regex;

final class Pattern$JavaDefined extends Pattern$JavaTypeClass {
    
    Pattern$JavaDefined() {
        
    }
    
    boolean isProperty(int ch) {
        return Character.isDefined(ch);
    }
}
