package java.util.regex;

final class Pattern$Specials extends Pattern$Node {
    
    Pattern$Specials() {
        
    }
    
    Pattern$Node dup(boolean not) {
        if (not) return new Pattern$Not(this); else return new Pattern$Specials();
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i < matcher.to) {
            int ch = seq.charAt(i);
            return (((ch - 65520) | (65533 - ch)) >= 0 || ch == 65279) && next.match(matcher, i + 1, seq);
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
