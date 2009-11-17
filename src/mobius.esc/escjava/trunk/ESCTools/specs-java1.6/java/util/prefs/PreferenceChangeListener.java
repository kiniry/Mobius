package java.util.prefs;

public interface PreferenceChangeListener extends java.util.EventListener {
    
    void preferenceChange(PreferenceChangeEvent evt);
}
