package java.util.regex;

final class Pattern$NotCtype extends Pattern$Node {
    int ctype;
    
    Pattern$NotCtype(int type) {
        
        ctype = type;
    }
    
    Pattern$Node dup(boolean not) {
        if (not) {
            return new Pattern$Ctype(ctype);
        } else {
            return new Pattern$NotCtype(ctype);
        }
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i >= matcher.to) {
            matcher.hitEnd = true;
            return false;
        }
        int c = Character.codePointAt(seq, i);
        return ((c >= 128 || !ASCII.isType(c, ctype)) && next.match(matcher, i + Character.charCount(c), seq));
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.minLength++;
        info.maxLength++;
        return next.study(info);
    }
}
