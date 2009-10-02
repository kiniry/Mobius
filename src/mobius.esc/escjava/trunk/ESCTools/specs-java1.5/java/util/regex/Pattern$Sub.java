package java.util.regex;

final class Pattern$Sub extends Pattern$Add {
    
    Pattern$Sub(Pattern$Node lhs, Pattern$Node rhs) {
        super(lhs, rhs);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i < matcher.to) {
            return !rhs.match(matcher, i, seq) && lhs.match(matcher, i, seq) && next.match(matcher, matcher.last, seq);
        }
        matcher.hitEnd = true;
        return false;
    }
    
    boolean study(Pattern$TreeInfo info) {
        lhs.study(info);
        return next.study(info);
    }
}
