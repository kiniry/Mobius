package java.util.regex;

final class Pattern$SliceU extends Pattern$Node {
    int[] buffer;
    
    Pattern$SliceU(int[] buf) {
        
        buffer = buf;
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
            int cc = Character.toUpperCase(c);
            cc = Character.toLowerCase(cc);
            if (buf[j] != cc) {
                return false;
            }
            x += Character.charCount(c);
            if (x > matcher.to) {
                matcher.hitEnd = true;
                return false;
            }
        }
        return next.match(matcher, x, seq);
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.minLength += buffer.length;
        info.maxLength += buffer.length;
        return next.study(info);
    }
}
