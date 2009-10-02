package java.util.prefs;

import java.security.PrivilegedAction;

class Preferences$2 implements PrivilegedAction {
    
    Preferences$2() {
        
    }
    
    public PreferencesFactory run() {
        return Preferences.access$000();
    }
    
    /*synthetic public Object run() {
        return this.run();
    } */
}
