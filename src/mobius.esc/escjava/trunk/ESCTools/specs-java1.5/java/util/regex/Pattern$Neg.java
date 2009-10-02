package java.util.regex;

final class Pattern$Neg extends Pattern$Node {
    Pattern$Node cond;
    
    Pattern$Neg(Pattern$Node cond) {
        
        this.cond = cond;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int savedTo = matcher.to;
        boolean conditionMatched = false;
        if (matcher.transparentBounds) matcher.to = matcher.getTextLength();
        try {
            if (i < matcher.to) {
                conditionMatched = !cond.match(matcher, i, seq);
            } else {
                matcher.requireEnd = true;
                conditionMatched = !cond.match(matcher, i, seq);
            }
        } finally {
            matcher.to = savedTo;
        }
        return conditionMatched && next.match(matcher, i, seq);
    }
}
