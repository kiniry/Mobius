package javax.print;

import java.util.Iterator;
import java.util.NoSuchElementException;

class MimeType$ParameterMapEntrySetIterator implements Iterator {
    
    /*synthetic*/ MimeType$ParameterMapEntrySetIterator(MimeType x0, javax.print.MimeType$1 x1) {
        this(x0);
    }
    /*synthetic*/ final MimeType this$0;
    
    private MimeType$ParameterMapEntrySetIterator(/*synthetic*/ final MimeType this$0) {
        this.this$0 = this$0;
        
    }
    private int myIndex = 2;
    
    public boolean hasNext() {
        return myIndex < MimeType.access$000(this$0).length;
    }
    
    public Object next() {
        if (hasNext()) {
            MimeType$ParameterMapEntry result = new MimeType$ParameterMapEntry(this$0, myIndex);
            myIndex += 2;
            return result;
        } else {
            throw new NoSuchElementException();
        }
    }
    
    public void remove() {
        throw new UnsupportedOperationException();
    }
}
