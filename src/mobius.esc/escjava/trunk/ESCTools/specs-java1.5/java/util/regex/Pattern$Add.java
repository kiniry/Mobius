package java.util.regex;

class Pattern$Add extends Pattern$Node {
    Pattern$Node lhs;
    Pattern$Node rhs;
    
    Pattern$Add(Pattern$Node lhs, Pattern$Node rhs) {
        
        this.lhs = lhs;
        this.rhs = rhs;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i < matcher.to) {
            return ((lhs.match(matcher, i, seq) || rhs.match(matcher, i, seq)) && next.match(matcher, matcher.last, seq));
        }
        matcher.hitEnd = true;
        return false;
    }
    
    boolean study(Pattern$TreeInfo info) {
        boolean maxV = info.maxValid;
        boolean detm = info.deterministic;
        int minL = info.minLength;
        int maxL = info.maxLength;
        lhs.study(info);
        int minL2 = info.minLength;
        int maxL2 = info.maxLength;
        info.minLength = minL;
        info.maxLength = maxL;
        rhs.study(info);
        info.minLength = Math.min(minL2, info.minLength);
        info.maxLength = Math.max(maxL2, info.maxLength);
        info.maxValid = maxV;
        info.deterministic = detm;
        return next.study(info);
    }
}
