package java.nio.charset;

import java.nio.*;

class CoderResult$2 extends CoderResult$Cache {
    
    CoderResult$2() {
        super(null);
    }
    
    public CoderResult create(int len) {
        return new CoderResult(3, len, null);
    }
}
