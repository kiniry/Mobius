package java.text;

import java.util.Locale;

final class BreakIterator$BreakIteratorCache {
    private BreakIterator iter;
    private Locale where;
    
    BreakIterator$BreakIteratorCache(Locale where, BreakIterator iter) {
        
        this.where = where;
        this.iter = (BreakIterator)(BreakIterator)iter.clone();
    }
    
    Locale getLocale() {
        return where;
    }
    
    BreakIterator createBreakInstance() {
        return (BreakIterator)(BreakIterator)iter.clone();
    }
}
