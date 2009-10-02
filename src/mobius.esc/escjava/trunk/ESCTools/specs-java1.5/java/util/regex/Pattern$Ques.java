package java.util.regex;

final class Pattern$Ques extends Pattern$Node {
    Pattern$Node atom;
    int type;
    
    Pattern$Ques(Pattern$Node node, int type) {
        
        this.atom = node;
        this.type = type;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        switch (type) {
        case 0: 
            return (atom.match(matcher, i, seq) && next.match(matcher, matcher.last, seq)) || next.match(matcher, i, seq);
        
        case 1: 
            return next.match(matcher, i, seq) || (atom.match(matcher, i, seq) && next.match(matcher, matcher.last, seq));
        
        case 2: 
            if (atom.match(matcher, i, seq)) i = matcher.last;
            return next.match(matcher, i, seq);
        
        default: 
            return atom.match(matcher, i, seq) && next.match(matcher, matcher.last, seq);
        
        }
    }
    
    boolean study(Pattern$TreeInfo info) {
        if (type != 3) {
            int minL = info.minLength;
            atom.study(info);
            info.minLength = minL;
            info.deterministic = false;
            return next.study(info);
        } else {
            atom.study(info);
            return next.study(info);
        }
    }
}
