package java.util.regex;

final class Pattern$GroupCurly extends Pattern$Node {
    Pattern$Node atom;
    int type;
    int cmin;
    int cmax;
    int localIndex;
    int groupIndex;
    boolean capture;
    
    Pattern$GroupCurly(Pattern$Node node, int cmin, int cmax, int type, int local, int group, boolean capture) {
        
        this.atom = node;
        this.type = type;
        this.cmin = cmin;
        this.cmax = cmax;
        this.localIndex = local;
        this.groupIndex = group;
        this.capture = capture;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int[] groups = matcher.groups;
        int[] locals = matcher.locals;
        int save0 = locals[localIndex];
        int save1 = 0;
        int save2 = 0;
        if (capture) {
            save1 = groups[groupIndex];
            save2 = groups[groupIndex + 1];
        }
        locals[localIndex] = -1;
        boolean ret = true;
        for (int j = 0; j < cmin; j++) {
            if (atom.match(matcher, i, seq)) {
                if (capture) {
                    groups[groupIndex] = i;
                    groups[groupIndex + 1] = matcher.last;
                }
                i = matcher.last;
            } else {
                ret = false;
                break;
            }
        }
        if (!ret) {
            locals[localIndex] = save0;
            if (capture) {
                groups[groupIndex] = save1;
                groups[groupIndex + 1] = save2;
            }
        } else if (type == 0) {
            ret = match0(matcher, i, cmin, seq);
        } else if (type == 1) {
            ret = match1(matcher, i, cmin, seq);
        } else {
            ret = match2(matcher, i, cmin, seq);
        }
        return ret;
    }
    
    boolean match0(Matcher matcher, int i, int j, CharSequence seq) {
        int[] groups = matcher.groups;
        int save0 = 0;
        int save1 = 0;
        if (capture) {
            save0 = groups[groupIndex];
            save1 = groups[groupIndex + 1];
        }
        for (; ; ) {
            if (j >= cmax) break;
            if (!atom.match(matcher, i, seq)) break;
            int k = matcher.last - i;
            if (k <= 0) {
                if (capture) {
                    groups[groupIndex] = i;
                    groups[groupIndex + 1] = i + k;
                }
                i = i + k;
                break;
            }
            for (; ; ) {
                if (capture) {
                    groups[groupIndex] = i;
                    groups[groupIndex + 1] = i + k;
                }
                i = i + k;
                if (++j >= cmax) break;
                if (!atom.match(matcher, i, seq)) break;
                if (i + k != matcher.last) {
                    if (match0(matcher, i, j, seq)) return true;
                    break;
                }
            }
            while (j > cmin) {
                if (next.match(matcher, i, seq)) {
                    if (capture) {
                        groups[groupIndex + 1] = i;
                        groups[groupIndex] = i - k;
                    }
                    i = i - k;
                    return true;
                }
                if (capture) {
                    groups[groupIndex + 1] = i;
                    groups[groupIndex] = i - k;
                }
                i = i - k;
                j--;
            }
            break;
        }
        if (capture) {
            groups[groupIndex] = save0;
            groups[groupIndex + 1] = save1;
        }
        return next.match(matcher, i, seq);
    }
    
    boolean match1(Matcher matcher, int i, int j, CharSequence seq) {
        for (; ; ) {
            if (next.match(matcher, i, seq)) return true;
            if (j >= cmax) return false;
            if (!atom.match(matcher, i, seq)) return false;
            if (i == matcher.last) return false;
            if (capture) {
                matcher.groups[groupIndex] = i;
                matcher.groups[groupIndex + 1] = matcher.last;
            }
            i = matcher.last;
            j++;
        }
    }
    
    boolean match2(Matcher matcher, int i, int j, CharSequence seq) {
        for (; j < cmax; j++) {
            if (!atom.match(matcher, i, seq)) {
                break;
            }
            if (capture) {
                matcher.groups[groupIndex] = i;
                matcher.groups[groupIndex + 1] = matcher.last;
            }
            if (i == matcher.last) {
                break;
            }
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
        if (info.deterministic && cmin == cmax) {
            info.deterministic = detm;
        } else {
            info.deterministic = false;
        }
        return next.study(info);
    }
}
