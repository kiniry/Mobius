package java.util.regex;

final class Pattern$UBlock extends Pattern$Node {
    Character$UnicodeBlock block;
    boolean complementMe = false;
    
    Pattern$UBlock() {
        
    }
    
    Pattern$UBlock(Character$UnicodeBlock block, boolean not) {
        
        this.block = block;
        this.complementMe = not;
    }
    
    Pattern$Node dup(boolean not) {
        if (not) return new Pattern$UBlock(block, !complementMe); else return new Pattern$UBlock(block, complementMe);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (complementMe) return notMatch(matcher, i, seq);
        if (i < matcher.to) {
            int ch = Character.codePointAt(seq, i);
            return (block == Character$UnicodeBlock.of(ch) && (next.match(matcher, i + Character.charCount(ch), seq)));
        }
        matcher.hitEnd = true;
        return false;
    }
    
    boolean notMatch(Matcher matcher, int i, CharSequence seq) {
        if (i < matcher.to) {
            int ch = Character.codePointAt(seq, i);
            return (block != Character$UnicodeBlock.of(ch) && (next.match(matcher, i + Character.charCount(ch), seq)));
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
