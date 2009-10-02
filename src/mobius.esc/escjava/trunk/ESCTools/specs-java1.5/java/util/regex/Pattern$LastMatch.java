package java.util.regex;

final class Pattern$LastMatch extends Pattern$Node {
    
    Pattern$LastMatch() {
        
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i != matcher.oldLast) return false;
        return next.match(matcher, i, seq);
    }
}
