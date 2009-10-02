package java.util.regex;

class Pattern$CIBackRef extends Pattern$Node {
    int groupIndex;
    
    Pattern$CIBackRef(int groupCount) {
        
        groupIndex = groupCount + groupCount;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int j = matcher.groups[groupIndex];
        int k = matcher.groups[groupIndex + 1];
        int groupSize = k - j;
        if (j < 0) return false;
        if (i + groupSize > matcher.to) {
            matcher.hitEnd = true;
            return false;
        }
        int x = i;
        for (int index = 0; index < groupSize; index++) {
            int c1 = Character.codePointAt(seq, x);
            int c2 = Character.codePointAt(seq, j);
            if (c1 != c2) {
                int cc1 = Character.toUpperCase(c1);
                int cc2 = Character.toUpperCase(c2);
                if (cc1 != cc2) {
                    cc1 = Character.toLowerCase(cc1);
                    cc2 = Character.toLowerCase(cc2);
                    if (cc1 != cc2) return false;
                }
            }
            x += Character.charCount(c1);
            j += Character.charCount(c2);
        }
        return next.match(matcher, i + groupSize, seq);
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.maxValid = false;
        return next.study(info);
    }
}
