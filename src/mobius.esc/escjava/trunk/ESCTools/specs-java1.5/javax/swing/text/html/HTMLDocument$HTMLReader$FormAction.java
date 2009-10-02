package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

public class HTMLDocument$HTMLReader$FormAction extends HTMLDocument$HTMLReader$SpecialAction {
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    public HTMLDocument$HTMLReader$FormAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
        this.this$1 = this$1;
        super(this$1);
    }
    
    public void start(HTML$Tag t, MutableAttributeSet attr) {
        if (t == HTML$Tag.INPUT) {
            String type = (String)(String)attr.getAttribute(HTML$Attribute.TYPE);
            if (type == null) {
                type = "text";
                attr.addAttribute(HTML$Attribute.TYPE, "text");
            }
            setModel(type, attr);
        } else if (t == HTML$Tag.TEXTAREA) {
            this$1.inTextArea = true;
            this$1.textAreaDocument = new TextAreaDocument();
            attr.addAttribute(StyleConstants.ModelAttribute, this$1.textAreaDocument);
        } else if (t == HTML$Tag.SELECT) {
            int size = HTML.getIntegerAttributeValue(attr, HTML$Attribute.SIZE, 1);
            boolean multiple = ((String)(String)attr.getAttribute(HTML$Attribute.MULTIPLE) != null);
            if ((size > 1) || multiple) {
                OptionListModel m = new OptionListModel();
                if (multiple) {
                    m.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);
                }
                selectModel = m;
            } else {
                selectModel = new OptionComboBoxModel();
            }
            attr.addAttribute(StyleConstants.ModelAttribute, selectModel);
        }
        if (t == HTML$Tag.OPTION) {
            this$1.option = new Option(attr);
            if (selectModel instanceof OptionListModel) {
                OptionListModel m = (OptionListModel)(OptionListModel)selectModel;
                m.addElement(this$1.option);
                if (this$1.option.isSelected()) {
                    m.addSelectionInterval(optionCount, optionCount);
                    m.setInitialSelection(optionCount);
                }
            } else if (selectModel instanceof OptionComboBoxModel) {
                OptionComboBoxModel m = (OptionComboBoxModel)(OptionComboBoxModel)selectModel;
                m.addElement(this$1.option);
                if (this$1.option.isSelected()) {
                    m.setSelectedItem(this$1.option);
                    m.setInitialSelection(this$1.option);
                }
            }
            optionCount++;
        } else {
            super.start(t, attr);
        }
    }
    
    public void end(HTML$Tag t) {
        if (t == HTML$Tag.OPTION) {
            this$1.option = null;
        } else {
            if (t == HTML$Tag.SELECT) {
                selectModel = null;
                optionCount = 0;
            } else if (t == HTML$Tag.TEXTAREA) {
                this$1.inTextArea = false;
                this$1.textAreaDocument.storeInitialText();
            }
            super.end(t);
        }
    }
    
    void setModel(String type, MutableAttributeSet attr) {
        if (type.equals("submit") || type.equals("reset") || type.equals("image")) {
            attr.addAttribute(StyleConstants.ModelAttribute, new DefaultButtonModel());
        } else if (type.equals("text") || type.equals("password")) {
            int maxLength = HTML.getIntegerAttributeValue(attr, HTML$Attribute.MAXLENGTH, -1);
            Document doc;
            if (maxLength > 0) {
                doc = new HTMLDocument$FixedLengthDocument(maxLength);
            } else {
                doc = new PlainDocument();
            }
            String value = (String)(String)attr.getAttribute(HTML$Attribute.VALUE);
            try {
                doc.insertString(0, value, null);
            } catch (BadLocationException e) {
            }
            attr.addAttribute(StyleConstants.ModelAttribute, doc);
        } else if (type.equals("file")) {
            attr.addAttribute(StyleConstants.ModelAttribute, new PlainDocument());
        } else if (type.equals("checkbox") || type.equals("radio")) {
            JToggleButton$ToggleButtonModel model = new JToggleButton$ToggleButtonModel();
            if (type.equals("radio")) {
                String name = (String)(String)attr.getAttribute(HTML$Attribute.NAME);
                if (HTMLDocument.access$700(this$1.this$0) == null) {
                    HTMLDocument.access$702(this$1.this$0, new HashMap());
                }
                ButtonGroup radioButtonGroup = (ButtonGroup)(ButtonGroup)HTMLDocument.access$700(this$1.this$0).get(name);
                if (radioButtonGroup == null) {
                    radioButtonGroup = new ButtonGroup();
                    HTMLDocument.access$700(this$1.this$0).put(name, radioButtonGroup);
                }
                model.setGroup(radioButtonGroup);
            }
            boolean checked = (attr.getAttribute(HTML$Attribute.CHECKED) != null);
            model.setSelected(checked);
            attr.addAttribute(StyleConstants.ModelAttribute, model);
        }
    }
    Object selectModel;
    int optionCount;
}
