package java.util.regex;

class Pattern$LastNode extends Pattern$Node {
    
    Pattern$LastNode() {
        
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (matcher.acceptMode == Matcher.ENDANCHOR && i != matcher.to) return false;
        matcher.last = i;
        matcher.groups[0] = matcher.first;
        matcher.groups[1] = matcher.last;
        return true;
    }
}
