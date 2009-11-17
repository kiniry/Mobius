package java.util.regex;

final class Pattern$Category extends Pattern$Node {
    int atype;
    
    Pattern$Category(int type) {
        
        atype = type;
    }
    
    Pattern$Node dup(boolean not) {
        return new Pattern$Category(not ? ~atype : atype);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i >= matcher.to) {
            matcher.hitEnd = true;
            return false;
        }
        int c = Character.codePointAt(seq, i);
        return (atype & (1 << Character.getType(c))) != 0 && next.match(matcher, i + Character.charCount(c), seq);
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.minLength++;
        info.maxLength++;
        return next.study(info);
    }
}
