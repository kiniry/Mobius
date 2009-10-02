package java.util.regex;

final class Pattern$Prolog extends Pattern$Node {
    Pattern$Loop loop;
    
    Pattern$Prolog(Pattern$Loop loop) {
        
        this.loop = loop;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        return loop.matchInit(matcher, i, seq);
    }
    
    boolean study(Pattern$TreeInfo info) {
        return loop.study(info);
    }
}
