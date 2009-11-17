package java.util.regex;

final class Pattern$SingleA extends Pattern$Node {
    int ch;
    
    Pattern$SingleA(int n) {
        
        ch = ASCII.toLower(n);
    }
    
    Pattern$Node dup(boolean not) {
        if (not) return new Pattern$NotSingleA(ch); else return new Pattern$SingleA(ch);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i >= matcher.to) {
            matcher.hitEnd = true;
        } else {
            int c = seq.charAt(i);
            if (c == ch || ASCII.toLower(c) == ch) {
                return next.match(matcher, i + 1, seq);
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
