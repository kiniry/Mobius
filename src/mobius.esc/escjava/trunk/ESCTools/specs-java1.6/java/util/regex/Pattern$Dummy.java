package java.util.regex;

class Pattern$Dummy extends Pattern$Node {
    
    Pattern$Dummy() {
        
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        return next.match(matcher, i, seq);
    }
}
