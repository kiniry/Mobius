package java.util.regex;

final class Pattern$SingleU extends Pattern$Node {
    int ch;
    int len;
    
    Pattern$SingleU(int c) {
        
        ch = Character.toLowerCase(Character.toUpperCase(c));
        len = Character.charCount(ch);
    }
    
    Pattern$Node dup(boolean not) {
        if (not) return new Pattern$NotSingleU(ch); else return new Pattern$SingleU(ch);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i >= matcher.to) {
            matcher.hitEnd = true;
        } else {
            int c = Character.codePointAt(seq, i);
            if (c == ch) return next.match(matcher, i + len, seq);
            int cc = Character.toUpperCase(c);
            cc = Character.toLowerCase(cc);
            if (cc == ch) return next.match(matcher, i + Character.charCount(c), seq);
        }
        return false;
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.minLength++;
        info.maxLength++;
        return next.study(info);
    }
}
