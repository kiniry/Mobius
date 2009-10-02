package java.util.regex;

final class Pattern$First extends Pattern$Node {
    Pattern$Node atom;
    
    Pattern$First(Pattern$Node node) {
        
        this.atom = Pattern$BnM.optimize(node);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (atom instanceof Pattern$BnM) {
            return atom.match(matcher, i, seq) && next.match(matcher, matcher.last, seq);
        }
        for (; ; ) {
            if (i > matcher.to) {
                matcher.hitEnd = true;
                return false;
            }
            if (atom.match(matcher, i, seq)) {
                return next.match(matcher, matcher.last, seq);
            }
            i += Pattern.access$000(seq, i, 1);
            matcher.first++;
        }
    }
    
    boolean study(Pattern$TreeInfo info) {
        atom.study(info);
        info.maxValid = false;
        info.deterministic = false;
        return next.study(info);
    }
}
