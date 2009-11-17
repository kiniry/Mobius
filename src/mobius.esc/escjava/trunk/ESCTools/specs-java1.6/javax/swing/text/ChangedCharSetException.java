package javax.swing.text;

import java.io.IOException;

public class ChangedCharSetException extends IOException {
    String charSetSpec;
    boolean charSetKey;
    
    public ChangedCharSetException(String charSetSpec, boolean charSetKey) {
        
        this.charSetSpec = charSetSpec;
        this.charSetKey = charSetKey;
    }
    
    public String getCharSetSpec() {
        return charSetSpec;
    }
    
    public boolean keyEqualsCharSet() {
        return charSetKey;
    }
}
