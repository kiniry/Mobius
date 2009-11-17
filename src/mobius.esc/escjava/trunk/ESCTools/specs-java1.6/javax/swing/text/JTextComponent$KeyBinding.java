package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.text.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JTextComponent$KeyBinding {
    public KeyStroke key;
    public String actionName;
    
    public JTextComponent$KeyBinding(KeyStroke key, String actionName) {
        
        this.key = key;
        this.actionName = actionName;
    }
}
