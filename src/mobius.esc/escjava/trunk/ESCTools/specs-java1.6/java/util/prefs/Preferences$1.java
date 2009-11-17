package java.util.prefs;

import java.security.PrivilegedAction;

class Preferences$1 implements PrivilegedAction {
    
    Preferences$1() {
        
    }
    
    public String run() {
        return System.getProperty("java.util.prefs.PreferencesFactory");
    }
    
    /*synthetic public Object run() {
        return this.run();
    } */
}
