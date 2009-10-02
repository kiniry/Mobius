package java.util.regex;

final class Pattern$CIRange extends Pattern$Range {
    
    Pattern$CIRange(int n) {
        
        lower = n >>> 16;
        upper = n & 65535;
    }
    
    Pattern$CIRange(int lower, int upper) {
        super(lower, upper);
    }
    
    Pattern$Node dup(boolean not) {
        if (not) return new Pattern$CINotRange(lower, upper); else return new Pattern$CIRange(lower, upper);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i < matcher.to) {
            int ch = Character.codePointAt(seq, i);
            boolean m = (((ch - lower) | (upper - ch)) >= 0);
            if (!m) {
                int cc = Character.toUpperCase(ch);
                m = (((cc - lower) | (upper - cc)) >= 0);
                if (!m) {
                    cc = Character.toLowerCase(cc);
                    m = (((cc - lower) | (upper - cc)) >= 0);
                }
            }
            return (m && next.match(matcher, i + Character.charCount(ch), seq));
        }
        matcher.hitEnd = true;
        return false;
    }
}
