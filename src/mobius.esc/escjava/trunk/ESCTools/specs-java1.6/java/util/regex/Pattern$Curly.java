package java.util.regex;

final class Pattern$Curly extends Pattern$Node {
    Pattern$Node atom;
    int type;
    int cmin;
    int cmax;
    
    Pattern$Curly(Pattern$Node node, int cmin, int cmax, int type) {
        
        this.atom = node;
        this.type = type;
        this.cmin = cmin;
        this.cmax = cmax;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int j;
        for (j = 0; j < cmin; j++) {
            if (atom.match(matcher, i, seq)) {
                i = matcher.last;
                continue;
            }
            return false;
        }
        if (type == 0) return match0(matcher, i, j, seq); else if (type == 1) return match1(matcher, i, j, seq); else return match2(matcher, i, j, seq);
    }
    
    boolean match0(Matcher matcher, int i, int j, CharSequence seq) {
        if (j >= cmax) {
            return next.match(matcher, i, seq);
        }
        int backLimit = j;
        while (atom.match(matcher, i, seq)) {
            int k = matcher.last - i;
            if (k == 0) break;
            i = matcher.last;
            j++;
            while (j < cmax) {
                if (!atom.match(matcher, i, seq)) break;
                if (i + k != matcher.last) {
                    if (match0(matcher, matcher.last, j + 1, seq)) return true;
                    break;
                }
                i += k;
                j++;
            }
            while (j >= backLimit) {
                if (next.match(matcher, i, seq)) return true;
                i -= k;
                j--;
            }
            return false;
        }
        return next.match(matcher, i, seq);
    }
    
    boolean match1(Matcher matcher, int i, int j, CharSequence seq) {
        for (; ; ) {
            if (next.match(matcher, i, seq)) return true;
            if (j >= cmax) return false;
            if (!atom.match(matcher, i, seq)) return false;
            if (i == matcher.last) return false;
            i = matcher.last;
            j++;
        }
    }
    
    boolean match2(Matcher matcher, int i, int j, CharSequence seq) {
        for (; j < cmax; j++) {
            if (!atom.match(matcher, i, seq)) break;
            if (i == matcher.last) break;
            i = matcher.last;
        }
        return next.match(matcher, i, seq);
    }
    
    boolean study(Pattern$TreeInfo info) {
        int minL = info.minLength;
        int maxL = info.maxLength;
        boolean maxV = info.maxValid;
        boolean detm = info.deterministic;
        info.reset();
        atom.study(info);
        int temp = info.minLength * cmin + minL;
        if (temp < minL) {
            temp = 268435455;
        }
        info.minLength = temp;
        if (maxV & info.maxValid) {
            temp = info.maxLength * cmax + maxL;
            info.maxLength = temp;
            if (temp < maxL) {
                info.maxValid = false;
            }
        } else {
            info.maxValid = false;
        }
        if (info.deterministic && cmin == cmax) info.deterministic = detm; else info.deterministic = false;
        return next.study(info);
    }
}
