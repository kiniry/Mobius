package java.util.regex;

final class Pattern$Ctype extends Pattern$Node {
    int ctype;
    
    Pattern$Ctype(int type) {
        
        ctype = type;
    }
    
    Pattern$Node dup(boolean not) {
        if (not) {
            return new Pattern$NotCtype(ctype);
        } else {
            return new Pattern$Ctype(ctype);
        }
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i >= matcher.to) {
            matcher.hitEnd = true;
            return false;
        }
        int c = Character.codePointAt(seq, i);
        return (c < 128 && ASCII.isType(c, ctype) && next.match(matcher, i + 1, seq));
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.minLength++;
        info.maxLength++;
        return next.study(info);
    }
}
