package java.util.regex;

final class Pattern$Single extends Pattern$Node {
    int ch;
    int len;
    
    Pattern$Single(int n) {
        
        ch = n;
        len = Character.charCount(ch);
    }
    
    Pattern$Node dup(boolean not) {
        if (not) return new Pattern$NotSingle(ch); else return new Pattern$Single(ch);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i >= matcher.to) {
            matcher.hitEnd = true;
            return false;
        }
        int c = Character.codePointAt(seq, i);
        return (c == ch && next.match(matcher, i + len, seq));
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.minLength++;
        info.maxLength++;
        return next.study(info);
    }
}
