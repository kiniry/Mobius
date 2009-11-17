package java.util.regex;

final class Pattern$Not extends Pattern$Node {
    Pattern$Node atom;
    
    Pattern$Not(Pattern$Node atom) {
        
        this.atom = atom;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i < matcher.to) return !atom.match(matcher, i, seq) && next.match(matcher, i + Pattern.access$000(seq, i, 1), seq);
        matcher.hitEnd = true;
        return false;
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.minLength++;
        info.maxLength++;
        return next.study(info);
    }
}
