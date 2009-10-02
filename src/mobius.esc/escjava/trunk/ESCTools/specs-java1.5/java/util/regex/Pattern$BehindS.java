package java.util.regex;

final class Pattern$BehindS extends Pattern$Behind {
    
    Pattern$BehindS(Pattern$Node cond, int rmax, int rmin) {
        super(cond, rmax, rmin);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int rmaxChars = Pattern.access$000(seq, i, -rmax);
        int rminChars = Pattern.access$000(seq, i, -rmin);
        int savedFrom = matcher.from;
        int startIndex = (!matcher.transparentBounds) ? matcher.from : 0;
        boolean conditionMatched = false;
        int from = Math.max(i - rmaxChars, startIndex);
        for (int j = i - rminChars; j >= from; j -= j > from ? Pattern.access$000(seq, j, -1) : 1) {
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
