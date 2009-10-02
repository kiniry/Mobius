package java.util.regex;

class Pattern$Range extends Pattern$Node {
    int lower;
    int upper;
    
    Pattern$Range() {
        
    }
    
    Pattern$Range(int n) {
        
        lower = n >>> 16;
        upper = n & 65535;
    }
    
    Pattern$Range(int lower, int upper) {
        
        this.lower = lower;
        this.upper = upper;
    }
    
    Pattern$Node dup(boolean not) {
        if (not) return new Pattern$NotRange(lower, upper); else return new Pattern$Range(lower, upper);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i < matcher.to) {
            int ch = Character.codePointAt(seq, i);
            return ((ch - lower) | (upper - ch)) >= 0 && next.match(matcher, i + Character.charCount(ch), seq);
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
