package java.util.regex;

final class Pattern$Begin extends Pattern$Node {
    
    Pattern$Begin() {
        
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int fromIndex = (matcher.anchoringBounds) ? matcher.from : 0;
        if (i == fromIndex && next.match(matcher, i, seq)) {
            matcher.first = i;
            matcher.groups[0] = i;
            matcher.groups[1] = matcher.last;
            return true;
        } else {
            return false;
        }
    }
}
