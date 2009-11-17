package java.beans;

public interface Visibility {
    
    boolean needsGui();
    
    void dontUseGui();
    
    void okToUseGui();
    
    boolean avoidingGui();
}
