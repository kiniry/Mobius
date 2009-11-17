package java.util.regex;

final class Pattern$Conditional extends Pattern$Node {
    Pattern$Node cond;
    Pattern$Node yes;
    Pattern$Node not;
    
    Pattern$Conditional(Pattern$Node cond, Pattern$Node yes, Pattern$Node not) {
        
        this.cond = cond;
        this.yes = yes;
        this.not = not;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (cond.match(matcher, i, seq)) {
            return yes.match(matcher, i, seq);
        } else {
            return not.match(matcher, i, seq);
        }
    }
    
    boolean study(Pattern$TreeInfo info) {
        int minL = info.minLength;
        int maxL = info.maxLength;
        boolean maxV = info.maxValid;
        info.reset();
        yes.study(info);
        int minL2 = info.minLength;
        int maxL2 = info.maxLength;
        boolean maxV2 = info.maxValid;
        info.reset();
        not.study(info);
        info.minLength = minL + Math.min(minL2, info.minLength);
        info.maxLength = maxL + Math.max(maxL2, info.maxLength);
        info.maxValid = (maxV & maxV2 & info.maxValid);
        info.deterministic = false;
        return next.study(info);
    }
}
