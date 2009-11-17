package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import javax.swing.text.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import java.util.*;
import javax.accessibility.*;
import java.lang.ref.*;

public abstract class HTMLEditorKit$Parser {
    
    public HTMLEditorKit$Parser() {
        
    }
    
    public abstract void parse(Reader r, HTMLEditorKit$ParserCallback cb, boolean ignoreCharSet) throws IOException;
}
