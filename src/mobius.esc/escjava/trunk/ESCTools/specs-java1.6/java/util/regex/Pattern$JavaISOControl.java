package java.util.regex;

final class Pattern$JavaISOControl extends Pattern$JavaTypeClass {
    
    Pattern$JavaISOControl() {
        
    }
    
    boolean isProperty(int ch) {
        return Character.isISOControl(ch);
    }
}
