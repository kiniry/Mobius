package java.util.regex;

final class Pattern$Branch extends Pattern$Node {
    Pattern$Node prev;
    
    Pattern$Branch(Pattern$Node lhs, Pattern$Node rhs) {
        
        this.prev = lhs;
        this.next = rhs;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        return (prev.match(matcher, i, seq) || next.match(matcher, i, seq));
    }
    
    boolean study(Pattern$TreeInfo info) {
        int minL = info.minLength;
        int maxL = info.maxLength;
        boolean maxV = info.maxValid;
        info.reset();
        prev.study(info);
        int minL2 = info.minLength;
        int maxL2 = info.maxLength;
        boolean maxV2 = info.maxValid;
        info.reset();
        next.study(info);
        info.minLength = minL + Math.min(minL2, info.minLength);
        info.maxLength = maxL + Math.max(maxL2, info.maxLength);
        info.maxValid = (maxV & maxV2 & info.maxValid);
        info.deterministic = false;
        return false;
    }
}
