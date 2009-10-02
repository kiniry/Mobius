package java.util.regex;

final class Pattern$Bound extends Pattern$Node {
    static int LEFT = 1;
    static int RIGHT = 2;
    static int BOTH = 3;
    static int NONE = 4;
    int type;
    
    Pattern$Bound(int n) {
        
        type = n;
    }
    
    int check(Matcher matcher, int i, CharSequence seq) {
        int ch;
        boolean left = false;
        int startIndex = matcher.from;
        int endIndex = matcher.to;
        if (matcher.transparentBounds) {
            startIndex = 0;
            endIndex = matcher.getTextLength();
        }
        if (i > startIndex) {
            ch = Character.codePointBefore(seq, i);
            left = (ch == '_' || Character.isLetterOrDigit(ch) || ((Character.getType(ch) == Character.NON_SPACING_MARK) && Pattern.access$100(matcher, i - 1, seq)));
        }
        boolean right = false;
        if (i < endIndex) {
            ch = Character.codePointAt(seq, i);
            right = (ch == '_' || Character.isLetterOrDigit(ch) || ((Character.getType(ch) == Character.NON_SPACING_MARK) && Pattern.access$100(matcher, i, seq)));
        } else {
            matcher.hitEnd = true;
            matcher.requireEnd = true;
        }
        return ((left ^ right) ? (right ? LEFT : RIGHT) : NONE);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        return (check(matcher, i, seq) & type) > 0 && next.match(matcher, i, seq);
    }
}
