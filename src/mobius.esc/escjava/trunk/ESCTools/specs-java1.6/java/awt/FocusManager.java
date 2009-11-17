package java.awt;

import java.awt.event.*;
import javax.accessibility.*;

class FocusManager implements java.io.Serializable {
    
    FocusManager() {
        
    }
    Container focusRoot;
    Component focusOwner;
    static final long serialVersionUID = 2491878825643557906L;
}
