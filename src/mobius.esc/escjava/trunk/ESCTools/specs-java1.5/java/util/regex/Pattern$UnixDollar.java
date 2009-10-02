package java.util.regex;

final class Pattern$UnixDollar extends Pattern$Node {
    boolean multiline;
    
    Pattern$UnixDollar(boolean mul) {
        
        multiline = mul;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int endIndex = (matcher.anchoringBounds) ? matcher.to : matcher.getTextLength();
        if (i < endIndex) {
            char ch = seq.charAt(i);
            if (ch == '\n') {
                if (multiline == false && i != endIndex - 1) return false;
                if (multiline) return next.match(matcher, i, seq);
            } else {
                return false;
            }
        }
        matcher.hitEnd = true;
        matcher.requireEnd = true;
        return next.match(matcher, i, seq);
    }
    
    boolean study(Pattern$TreeInfo info) {
        next.study(info);
        return info.deterministic;
    }
}
