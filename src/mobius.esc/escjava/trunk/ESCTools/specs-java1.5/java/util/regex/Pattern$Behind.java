package java.util.regex;

class Pattern$Behind extends Pattern$Node {
    Pattern$Node cond;
    int rmax;
    int rmin;
    
    Pattern$Behind(Pattern$Node cond, int rmax, int rmin) {
        
        this.cond = cond;
        this.rmax = rmax;
        this.rmin = rmin;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int savedFrom = matcher.from;
        boolean conditionMatched = false;
        int startIndex = (!matcher.transparentBounds) ? matcher.from : 0;
        int from = Math.max(i - rmax, startIndex);
        for (int j = i - rmin; j >= from; j--) {
            if (matcher.transparentBounds) matcher.from = 0;
            try {
                conditionMatched = (cond.match(matcher, j, seq) && matcher.last == i);
            } finally {
                matcher.from = savedFrom;
            }
            if (conditionMatched) return next.match(matcher, i, seq);
        }
        return false;
    }
}
