package java.util.regex;

class Pattern$BackRef extends Pattern$Node {
    int groupIndex;
    
    Pattern$BackRef(int groupCount) {
        
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
        for (int index = 0; index < groupSize; index++) if (seq.charAt(i + index) != seq.charAt(j + index)) return false;
        return next.match(matcher, i + groupSize, seq);
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.maxValid = false;
        return next.study(info);
    }
}
