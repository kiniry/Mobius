package java.util.regex;

class Pattern$Loop extends Pattern$Node {
    Pattern$Node body;
    int countIndex;
    int beginIndex;
    int cmin;
    int cmax;
    
    Pattern$Loop(int countIndex, int beginIndex) {
        
        this.countIndex = countIndex;
        this.beginIndex = beginIndex;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i > matcher.locals[beginIndex]) {
            int count = matcher.locals[countIndex];
            if (count < cmin) {
                matcher.locals[countIndex] = count + 1;
                boolean b = body.match(matcher, i, seq);
                if (!b) matcher.locals[countIndex] = count;
                return b;
            }
            if (count < cmax) {
                matcher.locals[countIndex] = count + 1;
                boolean b = body.match(matcher, i, seq);
                if (!b) matcher.locals[countIndex] = count; else return true;
            }
        }
        return next.match(matcher, i, seq);
    }
    
    boolean matchInit(Matcher matcher, int i, CharSequence seq) {
        int save = matcher.locals[countIndex];
        boolean ret = false;
        if (0 < cmin) {
            matcher.locals[countIndex] = 1;
            ret = body.match(matcher, i, seq);
        } else if (0 < cmax) {
            matcher.locals[countIndex] = 1;
            ret = body.match(matcher, i, seq);
            if (ret == false) ret = next.match(matcher, i, seq);
        } else {
            ret = next.match(matcher, i, seq);
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
