package java.util.regex;

final class Pattern$All extends Pattern$Node {
    
    Pattern$All() {
        
    }
    
    Pattern$Node dup(boolean not) {
        if (not) {
            return new Pattern$Single(-1);
        } else {
            return new Pattern$All();
        }
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i < matcher.to) {
            return next.match(matcher, i + Pattern.access$000(seq, i, 1), seq);
        }
        matcher.hitEnd = true;
        return false;
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.minLength++;
        info.maxLength++;
        return next.study(info);
    }
}
