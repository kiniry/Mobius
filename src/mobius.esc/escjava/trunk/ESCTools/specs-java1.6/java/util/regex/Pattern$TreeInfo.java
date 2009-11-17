package java.util.regex;

final class Pattern$TreeInfo {
    int minLength;
    int maxLength;
    boolean maxValid;
    boolean deterministic;
    
    Pattern$TreeInfo() {
        
        reset();
    }
    
    void reset() {
        minLength = 0;
        maxLength = 0;
        maxValid = true;
        deterministic = true;
    }
}
