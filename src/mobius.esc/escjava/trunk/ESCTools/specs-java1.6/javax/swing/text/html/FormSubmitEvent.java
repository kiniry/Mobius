package javax.swing.text.html;

import javax.swing.text.*;
import java.net.URL;

public class FormSubmitEvent extends HTMLFrameHyperlinkEvent {
    {
    }
    {
    }
    
    FormSubmitEvent(Object source, HyperlinkEvent$EventType type, URL targetURL, Element sourceElement, String targetFrame, FormSubmitEvent$MethodType method, String data) {
        super(source, type, targetURL, sourceElement, targetFrame);
        this.method = method;
        this.data = data;
    }
    
    public FormSubmitEvent$MethodType getMethod() {
        return method;
    }
    
    public String getData() {
        return data;
    }
    private FormSubmitEvent$MethodType method;
    private String data;
}
