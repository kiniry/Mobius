package java.awt;

import java.io.Serializable;

class CardLayout$Card implements Serializable {
    /*synthetic*/ final CardLayout this$0;
    static final long serialVersionUID = 6640330810709497518L;
    public String name;
    public Component comp;
    
    public CardLayout$Card(/*synthetic*/ final CardLayout this$0, String cardName, Component cardComponent) {
        this.this$0 = this$0;
        
        name = cardName;
        comp = cardComponent;
    }
}
