package java.util.regex;

final class Pattern$Dot extends Pattern$Node {
    
    Pattern$Dot() {
        
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i < matcher.to) {
            int ch = Character.codePointAt(seq, i);
            return (ch != '\n' && ch != '\r' && (ch | 1) != '\u2029' && ch != '\205' && next.match(matcher, i + Character.charCount(ch), seq));
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
