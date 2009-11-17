package java.util.regex;

final class Pattern$UnixDot extends Pattern$Node {
    
    Pattern$UnixDot() {
        
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i < matcher.to) {
            int ch = Character.codePointAt(seq, i);
            return (ch != '\n' && next.match(matcher, i + Character.charCount(ch), seq));
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
