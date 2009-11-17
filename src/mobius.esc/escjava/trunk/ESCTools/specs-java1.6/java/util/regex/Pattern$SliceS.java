package java.util.regex;

final class Pattern$SliceS extends Pattern$Slice {
    
    Pattern$SliceS(int[] buf) {
        super(buf);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int[] buf = buffer;
        int x = i;
        for (int j = 0; j < buf.length; j++) {
            if (x >= matcher.to) {
                matcher.hitEnd = true;
                return false;
            }
            int c = Character.codePointAt(seq, x);
            if (buf[j] != c) return false;
            x += Character.charCount(c);
            if (x > matcher.to) {
                matcher.hitEnd = true;
                return false;
            }
        }
        return next.match(matcher, x, seq);
    }
}
