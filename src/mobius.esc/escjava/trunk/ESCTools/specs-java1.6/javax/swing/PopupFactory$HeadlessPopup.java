package javax.swing;

import java.awt.*;

class PopupFactory$HeadlessPopup extends PopupFactory$ContainerPopup {
    
    private PopupFactory$HeadlessPopup() {
        super(null);
    }
    
    static Popup getHeadlessPopup(Component owner, Component contents, int ownerX, int ownerY) {
        PopupFactory$HeadlessPopup popup = new PopupFactory$HeadlessPopup();
        popup.reset(owner, contents, ownerX, ownerY);
        return popup;
    }
    
    Component createComponent(Component owner) {
        return new Panel(new BorderLayout());
    }
    
    public void show() {
    }
    
    public void hide() {
    }
}
