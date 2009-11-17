package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.text.*;
import java.awt.geom.*;
import java.beans.*;
import java.util.Enumeration;
import javax.swing.event.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import javax.swing.text.*;
import javax.swing.text.html.*;
import javax.swing.plaf.basic.*;
import java.util.*;

public abstract class AbstractButton$AccessibleAbstractButton extends JComponent$AccessibleJComponent implements AccessibleAction, AccessibleValue, AccessibleText, AccessibleExtendedComponent {
    /*synthetic*/ final AbstractButton this$0;
    
    protected AbstractButton$AccessibleAbstractButton(/*synthetic*/ final AbstractButton this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    public String getAccessibleName() {
        if (accessibleName != null) {
            return accessibleName;
        } else {
            if (this$0.getText() == null) {
                return super.getAccessibleName();
            } else {
                return this$0.getText();
            }
        }
    }
    
    public AccessibleIcon[] getAccessibleIcon() {
        Icon defaultIcon = this$0.getIcon();
        if (defaultIcon instanceof Accessible) {
            AccessibleContext ac = ((Accessible)(Accessible)defaultIcon).getAccessibleContext();
            if (ac != null && ac instanceof AccessibleIcon) {
                return new AccessibleIcon[]{(AccessibleIcon)(AccessibleIcon)ac};
            }
        }
        return null;
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        if (this$0.getModel().isArmed()) {
            states.add(AccessibleState.ARMED);
        }
        if (this$0.isFocusOwner()) {
            states.add(AccessibleState.FOCUSED);
        }
        if (this$0.getModel().isPressed()) {
            states.add(AccessibleState.PRESSED);
        }
        if (this$0.isSelected()) {
            states.add(AccessibleState.CHECKED);
        }
        return states;
    }
    
    public AccessibleRelationSet getAccessibleRelationSet() {
        AccessibleRelationSet relationSet = super.getAccessibleRelationSet();
        if (!relationSet.contains(AccessibleRelation.MEMBER_OF)) {
            ButtonModel model = this$0.getModel();
            if (model != null && model instanceof DefaultButtonModel) {
                ButtonGroup group = ((DefaultButtonModel)(DefaultButtonModel)model).getGroup();
                if (group != null) {
                    int len = group.getButtonCount();
                    Object[] target = new Object[len];
                    Enumeration elem = group.getElements();
                    for (int i = 0; i < len; i++) {
                        if (elem.hasMoreElements()) {
                            target[i] = elem.nextElement();
                        }
                    }
                    AccessibleRelation relation = new AccessibleRelation(AccessibleRelation.MEMBER_OF);
                    relation.setTarget(target);
                    relationSet.add(relation);
                }
            }
        }
        return relationSet;
    }
    
    public AccessibleAction getAccessibleAction() {
        return this;
    }
    
    public AccessibleValue getAccessibleValue() {
        return this;
    }
    
    public int getAccessibleActionCount() {
        return 1;
    }
    
    public String getAccessibleActionDescription(int i) {
        if (i == 0) {
            return UIManager.getString("AbstractButton.clickText");
        } else {
            return null;
        }
    }
    
    public boolean doAccessibleAction(int i) {
        if (i == 0) {
            this$0.doClick();
            return true;
        } else {
            return false;
        }
    }
    
    public Number getCurrentAccessibleValue() {
        if (this$0.isSelected()) {
            return new Integer(1);
        } else {
            return new Integer(0);
        }
    }
    
    public boolean setCurrentAccessibleValue(Number n) {
        if (n == null) {
            return false;
        }
        int i = n.intValue();
        if (i == 0) {
            this$0.setSelected(false);
        } else {
            this$0.setSelected(true);
        }
        return true;
    }
    
    public Number getMinimumAccessibleValue() {
        return new Integer(0);
    }
    
    public Number getMaximumAccessibleValue() {
        return new Integer(1);
    }
    
    public AccessibleText getAccessibleText() {
        View view = (View)(View)this$0.getClientProperty("html");
        if (view != null) {
            return this;
        } else {
            return null;
        }
    }
    
    public int getIndexAtPoint(Point p) {
        View view = (View)(View)this$0.getClientProperty("html");
        if (view != null) {
            Rectangle r = getTextRectangle();
            if (r == null) {
                return -1;
            }
            Rectangle2D$Float shape = new Rectangle2D$Float(r.x, r.y, r.width, r.height);
            Position$Bias[] bias = new Position$Bias[1];
            return view.viewToModel(p.x, p.y, shape, bias);
        } else {
            return -1;
        }
    }
    
    public Rectangle getCharacterBounds(int i) {
        View view = (View)(View)this$0.getClientProperty("html");
        if (view != null) {
            Rectangle r = getTextRectangle();
            if (r == null) {
                return null;
            }
            Rectangle2D$Float shape = new Rectangle2D$Float(r.x, r.y, r.width, r.height);
            try {
                Shape charShape = view.modelToView(i, shape, Position$Bias.Forward);
                return charShape.getBounds();
            } catch (BadLocationException e) {
                return null;
            }
        } else {
            return null;
        }
    }
    
    public int getCharCount() {
        View view = (View)(View)this$0.getClientProperty("html");
        if (view != null) {
            Document d = view.getDocument();
            if (d instanceof StyledDocument) {
                StyledDocument doc = (StyledDocument)(StyledDocument)d;
                return doc.getLength();
            }
        }
        return this$0.accessibleContext.getAccessibleName().length();
    }
    
    public int getCaretPosition() {
        return -1;
    }
    
    public String getAtIndex(int part, int index) {
        if (index < 0 || index >= getCharCount()) {
            return null;
        }
        switch (part) {
        case AccessibleText.CHARACTER: 
            try {
                return getText(index, 1);
            } catch (BadLocationException e) {
                return null;
            }
        
        case AccessibleText.WORD: 
            try {
                String s = getText(0, getCharCount());
                BreakIterator words = BreakIterator.getWordInstance(getLocale());
                words.setText(s);
                int end = words.following(index);
                return s.substring(words.previous(), end);
            } catch (BadLocationException e) {
                return null;
            }
        
        case AccessibleText.SENTENCE: 
            try {
                String s = getText(0, getCharCount());
                BreakIterator sentence = BreakIterator.getSentenceInstance(getLocale());
                sentence.setText(s);
                int end = sentence.following(index);
                return s.substring(sentence.previous(), end);
            } catch (BadLocationException e) {
                return null;
            }
        
        default: 
            return null;
        
        }
    }
    
    public String getAfterIndex(int part, int index) {
        if (index < 0 || index >= getCharCount()) {
            return null;
        }
        switch (part) {
        case AccessibleText.CHARACTER: 
            if (index + 1 >= getCharCount()) {
                return null;
            }
            try {
                return getText(index + 1, 1);
            } catch (BadLocationException e) {
                return null;
            }
        
        case AccessibleText.WORD: 
            try {
                String s = getText(0, getCharCount());
                BreakIterator words = BreakIterator.getWordInstance(getLocale());
                words.setText(s);
                int start = words.following(index);
                if (start == BreakIterator.DONE || start >= s.length()) {
                    return null;
                }
                int end = words.following(start);
                if (end == BreakIterator.DONE || end >= s.length()) {
                    return null;
                }
                return s.substring(start, end);
            } catch (BadLocationException e) {
                return null;
            }
        
        case AccessibleText.SENTENCE: 
            try {
                String s = getText(0, getCharCount());
                BreakIterator sentence = BreakIterator.getSentenceInstance(getLocale());
                sentence.setText(s);
                int start = sentence.following(index);
                if (start == BreakIterator.DONE || start >= s.length()) {
                    return null;
                }
                int end = sentence.following(start);
                if (end == BreakIterator.DONE || end >= s.length()) {
                    return null;
                }
                return s.substring(start, end);
            } catch (BadLocationException e) {
                return null;
            }
        
        default: 
            return null;
        
        }
    }
    
    public String getBeforeIndex(int part, int index) {
        if (index < 0 || index > getCharCount() - 1) {
            return null;
        }
        switch (part) {
        case AccessibleText.CHARACTER: 
            if (index == 0) {
                return null;
            }
            try {
                return getText(index - 1, 1);
            } catch (BadLocationException e) {
                return null;
            }
        
        case AccessibleText.WORD: 
            try {
                String s = getText(0, getCharCount());
                BreakIterator words = BreakIterator.getWordInstance(getLocale());
                words.setText(s);
                int end = words.following(index);
                end = words.previous();
                int start = words.previous();
                if (start == BreakIterator.DONE) {
                    return null;
                }
                return s.substring(start, end);
            } catch (BadLocationException e) {
                return null;
            }
        
        case AccessibleText.SENTENCE: 
            try {
                String s = getText(0, getCharCount());
                BreakIterator sentence = BreakIterator.getSentenceInstance(getLocale());
                sentence.setText(s);
                int end = sentence.following(index);
                end = sentence.previous();
                int start = sentence.previous();
                if (start == BreakIterator.DONE) {
                    return null;
                }
                return s.substring(start, end);
            } catch (BadLocationException e) {
                return null;
            }
        
        default: 
            return null;
        
        }
    }
    
    public AttributeSet getCharacterAttribute(int i) {
        View view = (View)(View)this$0.getClientProperty("html");
        if (view != null) {
            Document d = view.getDocument();
            if (d instanceof StyledDocument) {
                StyledDocument doc = (StyledDocument)(StyledDocument)d;
                Element elem = doc.getCharacterElement(i);
                if (elem != null) {
                    return elem.getAttributes();
                }
            }
        }
        return null;
    }
    
    public int getSelectionStart() {
        return -1;
    }
    
    public int getSelectionEnd() {
        return -1;
    }
    
    public String getSelectedText() {
        return null;
    }
    
    private String getText(int offset, int length) throws BadLocationException {
        View view = (View)(View)this$0.getClientProperty("html");
        if (view != null) {
            Document d = view.getDocument();
            if (d instanceof StyledDocument) {
                StyledDocument doc = (StyledDocument)(StyledDocument)d;
                return doc.getText(offset, length);
            }
        }
        return null;
    }
    
    private Rectangle getTextRectangle() {
        String text = this$0.getText();
        Icon icon = (this$0.isEnabled()) ? this$0.getIcon() : this$0.getDisabledIcon();
        if ((icon == null) && (text == null)) {
            return null;
        }
        Rectangle paintIconR = new Rectangle();
        Rectangle paintTextR = new Rectangle();
        Rectangle paintViewR = new Rectangle();
        Insets paintViewInsets = new Insets(0, 0, 0, 0);
        paintViewInsets = this$0.getInsets(paintViewInsets);
        paintViewR.x = paintViewInsets.left;
        paintViewR.y = paintViewInsets.top;
        paintViewR.width = this$0.getWidth() - (paintViewInsets.left + paintViewInsets.right);
        paintViewR.height = this$0.getHeight() - (paintViewInsets.top + paintViewInsets.bottom);
        Graphics g = this$0.getGraphics();
        if (g == null) {
            return null;
        }
        String clippedText = SwingUtilities.layoutCompoundLabel((JComponent)this$0, g.getFontMetrics(), text, icon, this$0.getVerticalAlignment(), this$0.getHorizontalAlignment(), this$0.getVerticalTextPosition(), this$0.getHorizontalTextPosition(), paintViewR, paintIconR, paintTextR, 0);
        return paintTextR;
    }
    
    AccessibleExtendedComponent getAccessibleExtendedComponent() {
        return this;
    }
    
    public String getToolTipText() {
        return this$0.getToolTipText();
    }
    
    public String getTitledBorderText() {
        return super.getTitledBorderText();
    }
    
    public AccessibleKeyBinding getAccessibleKeyBinding() {
        int mnemonic = this$0.getMnemonic();
        if (mnemonic == 0) {
            return null;
        }
        return new AbstractButton$AccessibleAbstractButton$ButtonKeyBinding(this, mnemonic);
    }
    {
    }
}
