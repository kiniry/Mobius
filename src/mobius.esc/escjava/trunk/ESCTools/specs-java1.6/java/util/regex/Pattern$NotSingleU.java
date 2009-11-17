package java.util.regex;

final class Pattern$NotSingleU extends Pattern$Node {
    int ch;
    
    Pattern$NotSingleU(int c) {
        
        ch = Character.toLowerCase(Character.toUpperCase((char)c));
    }
    
    Pattern$Node dup(boolean not) {
        if (not) return new Pattern$SingleU(ch); else return new Pattern$NotSingleU(ch);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i >= matcher.to) {
            matcher.hitEnd = true;
        } else {
            int c = Character.codePointAt(seq, i);
            if (c == ch) return false;
            int cc = Character.toUpperCase(c);
            cc = Character.toLowerCase(cc);
            if (cc != ch) return next.match(matcher, i + Character.charCount(c), seq);
        }
        return false;
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.minLength++;
        info.maxLength++;
        return next.study(info);
    }
}
