package java.awt.datatransfer;

import java.util.EventObject;

public class FlavorEvent extends EventObject {
    
    public FlavorEvent(Clipboard source) {
        super(source);
    }
}
