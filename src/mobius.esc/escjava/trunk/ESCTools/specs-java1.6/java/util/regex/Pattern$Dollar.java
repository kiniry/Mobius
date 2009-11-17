package java.util.regex;

final class Pattern$Dollar extends Pattern$Node {
    boolean multiline;
    
    Pattern$Dollar(boolean mul) {
        
        multiline = mul;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int endIndex = (matcher.anchoringBounds) ? matcher.to : matcher.getTextLength();
        if (!multiline) {
            if (i < endIndex - 2) return false;
            if (i == endIndex - 2) {
                char ch = seq.charAt(i);
                if (ch != '\r') return false;
                ch = seq.charAt(i + 1);
                if (ch != '\n') return false;
            }
        }
        if (i < endIndex) {
            char ch = seq.charAt(i);
            if (ch == '\n') {
                if (i > 0 && seq.charAt(i - 1) == '\r') return false;
                if (multiline) return next.match(matcher, i, seq);
            } else if (ch == '\r' || ch == '\205' || (ch | 1) == '\u2029') {
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
