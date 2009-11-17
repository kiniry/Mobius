package javax.swing.text.html;

import java.awt.*;
import java.util.*;
import java.net.*;
import java.io.*;
import javax.swing.*;
import javax.swing.text.*;
import javax.swing.event.*;

class FrameView$FrameEditorPane extends JEditorPane {
    
    /*synthetic*/ FrameView$FrameEditorPane(FrameView x0, javax.swing.text.html.FrameView$1 x1) {
        this(x0);
    }
    /*synthetic*/ final FrameView this$0;
    
    private FrameView$FrameEditorPane(/*synthetic*/ final FrameView this$0) {
        this.this$0 = this$0;
        
    }
    
    public EditorKit getEditorKitForContentType(String type) {
        EditorKit editorKit = super.getEditorKitForContentType(type);
        JEditorPane outerMostJEditorPane = null;
        if ((outerMostJEditorPane = FrameView.access$100(this$0)) != null) {
            EditorKit inheritedEditorKit = outerMostJEditorPane.getEditorKitForContentType(type);
            if (!editorKit.getClass().equals(inheritedEditorKit.getClass())) {
                editorKit = (EditorKit)(EditorKit)inheritedEditorKit.clone();
                setEditorKitForContentType(type, editorKit);
            }
        }
        return editorKit;
    }
}
