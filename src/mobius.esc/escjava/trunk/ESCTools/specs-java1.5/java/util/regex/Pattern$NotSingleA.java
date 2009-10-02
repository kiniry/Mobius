package java.util.regex;

final class Pattern$NotSingleA extends Pattern$Node {
    int ch;
    
    Pattern$NotSingleA(int n) {
        
        ch = ASCII.toLower(n);
    }
    
    Pattern$Node dup(boolean not) {
        if (not) return new Pattern$SingleA(ch); else return new Pattern$NotSingleA(ch);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i >= matcher.to) {
            matcher.hitEnd = true;
        } else {
            int c = Character.codePointAt(seq, i);
            if (c != ch && ASCII.toLower(c) != ch) {
                return next.match(matcher, i + Character.charCount(c), seq);
            }
        }
        return false;
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.minLength++;
        info.maxLength++;
        return next.study(info);
    }
}
