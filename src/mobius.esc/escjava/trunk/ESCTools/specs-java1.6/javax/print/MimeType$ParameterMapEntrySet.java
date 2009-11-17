package javax.print;

import java.util.AbstractSet;
import java.util.Iterator;

class MimeType$ParameterMapEntrySet extends AbstractSet {
    
    /*synthetic*/ MimeType$ParameterMapEntrySet(MimeType x0, javax.print.MimeType$1 x1) {
        this(x0);
    }
    /*synthetic*/ final MimeType this$0;
    
    private MimeType$ParameterMapEntrySet(/*synthetic*/ final MimeType this$0) {
        this.this$0 = this$0;
        
    }
    
    public Iterator iterator() {
        return new MimeType$ParameterMapEntrySetIterator(this$0, null);
    }
    
    public int size() {
        return (MimeType.access$000(this$0).length - 2) / 2;
    }
}
