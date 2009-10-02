package java.util.regex;

final class Pattern$GroupHead extends Pattern$Node {
    int localIndex;
    
    Pattern$GroupHead(int localCount) {
        
        localIndex = localCount;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int save = matcher.locals[localIndex];
        matcher.locals[localIndex] = i;
        boolean ret = next.match(matcher, i, seq);
        matcher.locals[localIndex] = save;
        return ret;
    }
    
    boolean matchRef(Matcher matcher, int i, CharSequence seq) {
        int save = matcher.locals[localIndex];
        matcher.locals[localIndex] = ~i;
        boolean ret = next.match(matcher, i, seq);
        matcher.locals[localIndex] = save;
        return ret;
    }
}
