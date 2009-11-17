package javax.print;

import java.util.AbstractMap;
import java.util.Set;

class MimeType$ParameterMap extends AbstractMap {
    
    /*synthetic*/ MimeType$ParameterMap(MimeType x0, javax.print.MimeType$1 x1) {
        this(x0);
    }
    /*synthetic*/ final MimeType this$0;
    
    private MimeType$ParameterMap(/*synthetic*/ final MimeType this$0) {
        this.this$0 = this$0;
        
    }
    
    public Set entrySet() {
        if (MimeType.access$200(this$0) == null) {
            MimeType.access$202(this$0, new MimeType$ParameterMapEntrySet(this$0, null));
        }
        return MimeType.access$200(this$0);
    }
}
