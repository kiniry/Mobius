package java.util.regex;

final class Pattern$NotSingle extends Pattern$Node {
    int ch;
    
    Pattern$NotSingle(int n) {
        
        ch = n;
    }
    
    Pattern$Node dup(boolean not) {
        if (not) return new Pattern$Single(ch); else return new Pattern$NotSingle(ch);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i >= matcher.to) {
            matcher.hitEnd = true;
            return false;
        }
        int c = Character.codePointAt(seq, i);
        return (c != ch && next.match(matcher, i + Character.charCount(c), seq));
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.minLength++;
        info.maxLength++;
        return next.study(info);
    }
}
