package java.util.regex;

class Pattern$Start extends Pattern$Node {
    int minLength;
    
    Pattern$Start(Pattern$Node node) {
        
        this.next = node;
        Pattern$TreeInfo info = new Pattern$TreeInfo();
        next.study(info);
        minLength = info.minLength;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i > matcher.to - minLength) {
            matcher.hitEnd = true;
            return false;
        }
        boolean ret = false;
        int guard = matcher.to - minLength;
        for (; i <= guard; i++) {
            if (ret = next.match(matcher, i, seq)) break;
            if (i == guard) matcher.hitEnd = true;
        }
        if (ret) {
            matcher.first = i;
            matcher.groups[0] = matcher.first;
            matcher.groups[1] = matcher.last;
        }
        return ret;
    }
    
    boolean study(Pattern$TreeInfo info) {
        next.study(info);
        info.maxValid = false;
        info.deterministic = false;
        return false;
    }
}
