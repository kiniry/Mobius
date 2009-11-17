package java.util.regex;

final class Pattern$UnixCaret extends Pattern$Node {
    
    Pattern$UnixCaret() {
        
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
            if (ch != '\n') {
                return false;
            }
        }
        return next.match(matcher, i, seq);
    }
}
