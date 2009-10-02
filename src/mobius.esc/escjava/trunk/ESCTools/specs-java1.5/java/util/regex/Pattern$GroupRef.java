package java.util.regex;

final class Pattern$GroupRef extends Pattern$Node {
    Pattern$GroupHead head;
    
    Pattern$GroupRef(Pattern$GroupHead head) {
        
        this.head = head;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        return head.matchRef(matcher, i, seq) && next.match(matcher, matcher.last, seq);
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.maxValid = false;
        info.deterministic = false;
        return next.study(info);
    }
}
