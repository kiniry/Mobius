package java.util.regex;

final class Pattern$Caret extends Pattern$Node {
    
    Pattern$Caret() {
        
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int startIndex = matcher.from;
        int endIndex = matcher.to;
        if (!matcher.anchoringBounds) {
            startIndex = 0;
            endIndex = matcher.getTextLength();
        }
        if (i == endIndex) {
            matcher.hitEnd = true;
            return false;
        }
        if (i > startIndex) {
            char ch = seq.charAt(i - 1);
            if (ch != '\n' && ch != '\r' && (ch | 1) != '\u2029' && ch != '\205') {
                return false;
            }
            if (ch == '\r' && seq.charAt(i) == '\n') return false;
        }
        return next.match(matcher, i, seq);
    }
}
