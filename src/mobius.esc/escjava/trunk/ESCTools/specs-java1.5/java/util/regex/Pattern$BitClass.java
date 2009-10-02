package java.util.regex;

final class Pattern$BitClass extends Pattern$Node {
    boolean[] bits = new boolean[256];
    boolean complementMe = false;
    
    Pattern$BitClass(boolean not) {
        
        complementMe = not;
    }
    
    Pattern$BitClass(boolean[] newBits, boolean not) {
        
        complementMe = not;
        bits = newBits;
    }
    
    Pattern$Node add(int c, int f) {
        if ((f & 2) == 0) {
            bits[c] = true;
        } else if (ASCII.isAscii(c)) {
            bits[ASCII.toUpper(c)] = true;
            bits[ASCII.toLower(c)] = true;
        } else {
            bits[Character.toLowerCase((char)c)] = true;
            bits[Character.toUpperCase((char)c)] = true;
        }
        return this;
    }
    
    Pattern$Node dup(boolean not) {
        return new Pattern$BitClass(bits, not);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i >= matcher.to) {
            matcher.hitEnd = true;
            return false;
        }
        int c = Character.codePointAt(seq, i);
        boolean charMatches = (c > 255) ? complementMe : (bits[c] ^ complementMe);
        return charMatches && next.match(matcher, i + Character.charCount(c), seq);
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.minLength++;
        info.maxLength++;
        return next.study(info);
    }
}
