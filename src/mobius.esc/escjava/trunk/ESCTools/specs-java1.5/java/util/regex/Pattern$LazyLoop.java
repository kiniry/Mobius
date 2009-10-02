package java.util.regex;

final class Pattern$LazyLoop extends Pattern$Loop {
    
    Pattern$LazyLoop(int countIndex, int beginIndex) {
        super(countIndex, beginIndex);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i > matcher.locals[beginIndex]) {
            int count = matcher.locals[countIndex];
            if (count < cmin) {
                matcher.locals[countIndex] = count + 1;
                boolean result = body.match(matcher, i, seq);
                if (!result) matcher.locals[countIndex] = count;
                return result;
            }
            if (next.match(matcher, i, seq)) return true;
            if (count < cmax) {
                matcher.locals[countIndex] = count + 1;
                boolean result = body.match(matcher, i, seq);
                if (!result) matcher.locals[countIndex] = count;
                return result;
            }
            return false;
        }
        return next.match(matcher, i, seq);
    }
    
    boolean matchInit(Matcher matcher, int i, CharSequence seq) {
        int save = matcher.locals[countIndex];
        boolean ret = false;
        if (0 < cmin) {
            matcher.locals[countIndex] = 1;
            ret = body.match(matcher, i, seq);
        } else if (next.match(matcher, i, seq)) {
            ret = true;
        } else if (0 < cmax) {
            matcher.locals[countIndex] = 1;
            ret = body.match(matcher, i, seq);
        }
        matcher.locals[countIndex] = save;
        return ret;
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.maxValid = false;
        info.deterministic = false;
        return false;
    }
}
