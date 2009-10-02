package java.nio.charset;

import java.nio.*;

class CoderResult$1 extends CoderResult$Cache {
    
    CoderResult$1() {
        super(null);
    }
    
    public CoderResult create(int len) {
        return new CoderResult(2, len, null);
    }
}
