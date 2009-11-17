package java.awt;

import java.util.logging.*;

class DefaultKeyboardFocusManager$TypeAheadMarker {
    long after;
    Component untilFocused;
    
    DefaultKeyboardFocusManager$TypeAheadMarker(long after, Component untilFocused) {
        
        this.after = after;
        this.untilFocused = untilFocused;
    }
    
    public String toString() {
        return ">>> Marker after " + after + " on " + untilFocused;
    }
}
