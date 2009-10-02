package java.util.regex;

class Pattern$Node extends Object {
    Pattern$Node next;
    
    Pattern$Node() {
        
        next = Pattern.accept;
    }
    
    Pattern$Node dup(boolean not) {
        if (not) {
            return new Pattern$Not(this);
        } else {
            throw new RuntimeException("internal error in Node dup()");
        }
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        matcher.last = i;
        matcher.groups[0] = matcher.first;
        matcher.groups[1] = matcher.last;
        return true;
    }
    
    boolean study(Pattern$TreeInfo info) {
        if (next != null) {
            return next.study(info);
        } else {
            return info.deterministic;
        }
    }
}
