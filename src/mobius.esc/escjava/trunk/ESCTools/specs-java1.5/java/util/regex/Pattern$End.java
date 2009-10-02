package java.util.regex;

final class Pattern$End extends Pattern$Node {
    
    Pattern$End() {
        
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int endIndex = (matcher.anchoringBounds) ? matcher.to : matcher.getTextLength();
        if (i == endIndex) {
            matcher.hitEnd = true;
            return next.match(matcher, i, seq);
        }
        return false;
    }
}
