package java.util.regex;

final class Pattern$Pos extends Pattern$Node {
    Pattern$Node cond;
    
    Pattern$Pos(Pattern$Node cond) {
        
        this.cond = cond;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int savedTo = matcher.to;
        boolean conditionMatched = false;
        if (matcher.transparentBounds) matcher.to = matcher.getTextLength();
        try {
            conditionMatched = cond.match(matcher, i, seq);
        } finally {
            matcher.to = savedTo;
        }
        return conditionMatched && next.match(matcher, i, seq);
    }
}
