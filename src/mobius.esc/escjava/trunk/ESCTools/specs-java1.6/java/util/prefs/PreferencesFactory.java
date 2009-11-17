package java.util.prefs;

import java.util.*;

public interface PreferencesFactory {
    
    Preferences systemRoot();
    
    Preferences userRoot();
}
