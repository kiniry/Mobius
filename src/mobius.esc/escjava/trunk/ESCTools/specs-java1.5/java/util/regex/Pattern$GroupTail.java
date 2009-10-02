package java.util.regex;

final class Pattern$GroupTail extends Pattern$Node {
    int localIndex;
    int groupIndex;
    
    Pattern$GroupTail(int localCount, int groupCount) {
        
        localIndex = localCount;
        groupIndex = groupCount + groupCount;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int tmp = matcher.locals[localIndex];
        if (tmp >= 0) {
            int groupStart = matcher.groups[groupIndex];
            int groupEnd = matcher.groups[groupIndex + 1];
            matcher.groups[groupIndex] = tmp;
            matcher.groups[groupIndex + 1] = i;
            if (next.match(matcher, i, seq)) {
                return true;
            }
            matcher.groups[groupIndex] = groupStart;
            matcher.groups[groupIndex + 1] = groupEnd;
            return false;
        } else {
            matcher.last = i;
            return true;
        }
    }
}
