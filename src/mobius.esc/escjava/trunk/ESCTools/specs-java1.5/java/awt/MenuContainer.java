package java.awt;

public interface MenuContainer {
    
    Font getFont();
    
    void remove(MenuComponent comp);
    
    
    boolean postEvent(Event evt);
}
