package javax.swing.text.html;

import java.net.*;
import java.io.*;
import java.awt.*;
import java.awt.event.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;

public class FormView extends ComponentView implements ActionListener {
    
    /*synthetic*/ static String access$200(FormView x0, Point x1) {
        return x0.getImageData(x1);
    }
    
    /*synthetic*/ static Element access$000(FormView x0) {
        return x0.getFormElement();
    }
    
    public static final String SUBMIT = new String("Submit Query");
    
    public static final String RESET = new String("Reset");
    private short maxIsPreferred;
    
    public FormView(Element elem) {
        super(elem);
    }
    
    protected Component createComponent() {
        AttributeSet attr = getElement().getAttributes();
        HTML$Tag t = (HTML$Tag)(HTML$Tag)attr.getAttribute(StyleConstants.NameAttribute);
        JComponent c = null;
        Object model = attr.getAttribute(StyleConstants.ModelAttribute);
        if (t == HTML$Tag.INPUT) {
            c = createInputComponent(attr, model);
        } else if (t == HTML$Tag.SELECT) {
            if (model instanceof OptionListModel) {
                JList list = new JList((ListModel)(ListModel)model);
                int size = HTML.getIntegerAttributeValue(attr, HTML$Attribute.SIZE, 1);
                list.setVisibleRowCount(size);
                list.setSelectionModel((ListSelectionModel)(ListSelectionModel)model);
                c = new JScrollPane(list);
            } else {
                c = new JComboBox((ComboBoxModel)(ComboBoxModel)model);
                maxIsPreferred = 3;
            }
        } else if (t == HTML$Tag.TEXTAREA) {
            JTextArea area = new JTextArea((Document)(Document)model);
            int rows = HTML.getIntegerAttributeValue(attr, HTML$Attribute.ROWS, 1);
            area.setRows(rows);
            int cols = HTML.getIntegerAttributeValue(attr, HTML$Attribute.COLS, 20);
            maxIsPreferred = 3;
            area.setColumns(cols);
            c = new JScrollPane(area, JScrollPane.VERTICAL_SCROLLBAR_ALWAYS, JScrollPane.HORIZONTAL_SCROLLBAR_ALWAYS);
        }
        if (c != null) {
            c.setAlignmentY(1.0F);
        }
        return c;
    }
    
    private JComponent createInputComponent(AttributeSet attr, Object model) {
        JComponent c = null;
        String type = (String)(String)attr.getAttribute(HTML$Attribute.TYPE);
        if (type.equals("submit") || type.equals("reset")) {
            String value = (String)(String)attr.getAttribute(HTML$Attribute.VALUE);
            if (value == null) {
                if (type.equals("submit")) {
                    value = UIManager.getString("FormView.submitButtonText");
                } else {
                    value = UIManager.getString("FormView.resetButtonText");
                }
            }
            JButton button = new JButton(value);
            if (model != null) {
                button.setModel((ButtonModel)(ButtonModel)model);
                button.addActionListener(this);
            }
            c = button;
            maxIsPreferred = 3;
        } else if (type.equals("image")) {
            String srcAtt = (String)(String)attr.getAttribute(HTML$Attribute.SRC);
            JButton button;
            try {
                URL base = ((HTMLDocument)(HTMLDocument)getElement().getDocument()).getBase();
                URL srcURL = new URL(base, srcAtt);
                Icon icon = new ImageIcon(srcURL);
                button = new JButton(icon);
            } catch (MalformedURLException e) {
                button = new JButton(srcAtt);
            }
            if (model != null) {
                button.setModel((ButtonModel)(ButtonModel)model);
                button.addMouseListener(new FormView$MouseEventListener(this));
            }
            c = button;
            maxIsPreferred = 3;
        } else if (type.equals("checkbox")) {
            c = new JCheckBox();
            if (model != null) {
                ((JCheckBox)(JCheckBox)c).setModel((JToggleButton$ToggleButtonModel)(JToggleButton$ToggleButtonModel)model);
            }
            maxIsPreferred = 3;
        } else if (type.equals("radio")) {
            c = new JRadioButton();
            if (model != null) {
                ((JRadioButton)(JRadioButton)c).setModel((JToggleButton$ToggleButtonModel)(JToggleButton$ToggleButtonModel)model);
            }
            maxIsPreferred = 3;
        } else if (type.equals("text")) {
            int size = HTML.getIntegerAttributeValue(attr, HTML$Attribute.SIZE, -1);
            JTextField field;
            if (size > 0) {
                field = new JTextField();
                field.setColumns(size);
            } else {
                field = new JTextField();
                field.setColumns(20);
            }
            c = field;
            if (model != null) {
                field.setDocument((Document)(Document)model);
            }
            field.addActionListener(this);
            maxIsPreferred = 3;
        } else if (type.equals("password")) {
            JPasswordField field = new JPasswordField();
            c = field;
            if (model != null) {
                field.setDocument((Document)(Document)model);
            }
            int size = HTML.getIntegerAttributeValue(attr, HTML$Attribute.SIZE, -1);
            field.setColumns((size > 0) ? size : 20);
            field.addActionListener(this);
            maxIsPreferred = 3;
        } else if (type.equals("file")) {
            JTextField field = new JTextField();
            if (model != null) {
                field.setDocument((Document)(Document)model);
            }
            int size = HTML.getIntegerAttributeValue(attr, HTML$Attribute.SIZE, -1);
            field.setColumns((size > 0) ? size : 20);
            JButton browseButton = new JButton(UIManager.getString("FormView.browseFileButtonText"));
            Box box = Box.createHorizontalBox();
            box.add(field);
            box.add(Box.createHorizontalStrut(5));
            box.add(browseButton);
            browseButton.addActionListener(new FormView$BrowseFileAction(this, attr, (Document)(Document)model));
            c = box;
            maxIsPreferred = 3;
        }
        return c;
    }
    
    public float getMaximumSpan(int axis) {
        switch (axis) {
        case View.X_AXIS: 
            if ((maxIsPreferred & 1) == 1) {
                super.getMaximumSpan(axis);
                return getPreferredSpan(axis);
            }
            return super.getMaximumSpan(axis);
        
        case View.Y_AXIS: 
            if ((maxIsPreferred & 2) == 2) {
                super.getMaximumSpan(axis);
                return getPreferredSpan(axis);
            }
            return super.getMaximumSpan(axis);
        
        default: 
            break;
        
        }
        return super.getMaximumSpan(axis);
    }
    
    public void actionPerformed(ActionEvent evt) {
        Element element = getElement();
        StringBuffer dataBuffer = new StringBuffer();
        HTMLDocument doc = (HTMLDocument)(HTMLDocument)getDocument();
        AttributeSet attr = element.getAttributes();
        String type = (String)(String)attr.getAttribute(HTML$Attribute.TYPE);
        if (type.equals("submit")) {
            getFormData(dataBuffer);
            submitData(dataBuffer.toString());
        } else if (type.equals("reset")) {
            resetForm();
        } else if (type.equals("text") || type.equals("password")) {
            if (isLastTextOrPasswordField()) {
                getFormData(dataBuffer);
                submitData(dataBuffer.toString());
            } else {
                getComponent().transferFocus();
            }
        }
    }
    
    protected void submitData(String data) {
        FormView$SubmitThread dataThread = new FormView$SubmitThread(this, getElement(), data);
        dataThread.start();
    }
    {
    }
    {
    }
    
    protected void imageSubmit(String imageData) {
        StringBuffer dataBuffer = new StringBuffer();
        Element elem = getElement();
        HTMLDocument hdoc = (HTMLDocument)(HTMLDocument)elem.getDocument();
        getFormData(dataBuffer);
        if (dataBuffer.length() > 0) {
            dataBuffer.append('&');
        }
        dataBuffer.append(imageData);
        submitData(dataBuffer.toString());
        return;
    }
    
    private String getImageData(Point point) {
        String mouseCoords = point.x + ":" + point.y;
        int sep = mouseCoords.indexOf(':');
        String x = mouseCoords.substring(0, sep);
        String y = mouseCoords.substring(++sep);
        String name = (String)(String)getElement().getAttributes().getAttribute(HTML$Attribute.NAME);
        String data;
        if (name == null || name.equals("")) {
            data = "x=" + x + "&y=" + y;
        } else {
            name = URLEncoder.encode(name);
            data = name + ".x" + "=" + x + "&" + name + ".y" + "=" + y;
        }
        return data;
    }
    
    private Element getFormElement() {
        Element elem = getElement();
        while (elem != null) {
            if (elem.getAttributes().getAttribute(StyleConstants.NameAttribute) == HTML$Tag.FORM) {
                return elem;
            }
            elem = elem.getParentElement();
        }
        return null;
    }
    
    void getFormData(StringBuffer buffer) {
        Element formE = getFormElement();
        if (formE != null) {
            ElementIterator it = new ElementIterator(formE);
            Element next;
            while ((next = it.next()) != null) {
                if (isControl(next)) {
                    String type = (String)(String)next.getAttributes().getAttribute(HTML$Attribute.TYPE);
                    if (type != null && type.equals("submit") && next != getElement()) {
                    } else if (type == null || !type.equals("image")) {
                        loadElementDataIntoBuffer(next, buffer);
                    }
                }
            }
        }
    }
    
    private void loadElementDataIntoBuffer(Element elem, StringBuffer buffer) {
        AttributeSet attr = elem.getAttributes();
        String name = (String)(String)attr.getAttribute(HTML$Attribute.NAME);
        if (name == null) {
            return;
        }
        String value = null;
        HTML$Tag tag = (HTML$Tag)(HTML$Tag)elem.getAttributes().getAttribute(StyleConstants.NameAttribute);
        if (tag == HTML$Tag.INPUT) {
            value = getInputElementData(attr);
        } else if (tag == HTML$Tag.TEXTAREA) {
            value = getTextAreaData(attr);
        } else if (tag == HTML$Tag.SELECT) {
            loadSelectData(attr, buffer);
        }
        if (name != null && value != null) {
            appendBuffer(buffer, name, value);
        }
    }
    
    private String getInputElementData(AttributeSet attr) {
        Object model = attr.getAttribute(StyleConstants.ModelAttribute);
        String type = (String)(String)attr.getAttribute(HTML$Attribute.TYPE);
        String value = null;
        if (type.equals("text") || type.equals("password")) {
            Document doc = (Document)(Document)model;
            try {
                value = doc.getText(0, doc.getLength());
            } catch (BadLocationException e) {
                value = null;
            }
        } else if (type.equals("submit") || type.equals("hidden")) {
            value = (String)(String)attr.getAttribute(HTML$Attribute.VALUE);
            if (value == null) {
                value = "";
            }
        } else if (type.equals("radio") || type.equals("checkbox")) {
            ButtonModel m = (ButtonModel)(ButtonModel)model;
            if (m.isSelected()) {
                value = (String)(String)attr.getAttribute(HTML$Attribute.VALUE);
                if (value == null) {
                    value = "on";
                }
            }
        } else if (type.equals("file")) {
            Document doc = (Document)(Document)model;
            String path;
            try {
                path = doc.getText(0, doc.getLength());
            } catch (BadLocationException e) {
                path = null;
            }
            if (path != null && path.length() > 0) {
                value = path;
            }
        }
        return value;
    }
    
    private String getTextAreaData(AttributeSet attr) {
        Document doc = (Document)(Document)attr.getAttribute(StyleConstants.ModelAttribute);
        try {
            return doc.getText(0, doc.getLength());
        } catch (BadLocationException e) {
            return null;
        }
    }
    
    private void loadSelectData(AttributeSet attr, StringBuffer buffer) {
        String name = (String)(String)attr.getAttribute(HTML$Attribute.NAME);
        if (name == null) {
            return;
        }
        Object m = attr.getAttribute(StyleConstants.ModelAttribute);
        if (m instanceof OptionListModel) {
            OptionListModel model = (OptionListModel)(OptionListModel)m;
            for (int i = 0; i < model.getSize(); i++) {
                if (model.isSelectedIndex(i)) {
                    Option option = (Option)(Option)model.getElementAt(i);
                    appendBuffer(buffer, name, option.getValue());
                }
            }
        } else if (m instanceof ComboBoxModel) {
            ComboBoxModel model = (ComboBoxModel)(ComboBoxModel)m;
            Option option = (Option)(Option)model.getSelectedItem();
            if (option != null) {
                appendBuffer(buffer, name, option.getValue());
            }
        }
    }
    
    private void appendBuffer(StringBuffer buffer, String name, String value) {
        if (buffer.length() > 0) {
            buffer.append('&');
        }
        String encodedName = URLEncoder.encode(name);
        buffer.append(encodedName);
        buffer.append('=');
        String encodedValue = URLEncoder.encode(value);
        buffer.append(encodedValue);
    }
    
    private boolean isControl(Element elem) {
        return elem.isLeaf();
    }
    
    boolean isLastTextOrPasswordField() {
        Element parent = getFormElement();
        Element elem = getElement();
        if (parent != null) {
            ElementIterator it = new ElementIterator(parent);
            Element next;
            boolean found = false;
            while ((next = it.next()) != null) {
                if (next == elem) {
                    found = true;
                } else if (found && isControl(next)) {
                    AttributeSet elemAttr = next.getAttributes();
                    if (HTMLDocument.matchNameAttribute(elemAttr, HTML$Tag.INPUT)) {
                        String type = (String)(String)elemAttr.getAttribute(HTML$Attribute.TYPE);
                        if ("text".equals(type) || "password".equals(type)) {
                            return false;
                        }
                    }
                }
            }
        }
        return true;
    }
    
    void resetForm() {
        Element parent = getFormElement();
        if (parent != null) {
            ElementIterator it = new ElementIterator(parent);
            Element next;
            while ((next = it.next()) != null) {
                if (isControl(next)) {
                    AttributeSet elemAttr = next.getAttributes();
                    Object m = elemAttr.getAttribute(StyleConstants.ModelAttribute);
                    if (m instanceof TextAreaDocument) {
                        TextAreaDocument doc = (TextAreaDocument)(TextAreaDocument)m;
                        doc.reset();
                    } else if (m instanceof PlainDocument) {
                        try {
                            PlainDocument doc = (PlainDocument)(PlainDocument)m;
                            doc.remove(0, doc.getLength());
                            if (HTMLDocument.matchNameAttribute(elemAttr, HTML$Tag.INPUT)) {
                                String value = (String)(String)elemAttr.getAttribute(HTML$Attribute.VALUE);
                                if (value != null) {
                                    doc.insertString(0, value, null);
                                }
                            }
                        } catch (BadLocationException e) {
                        }
                    } else if (m instanceof OptionListModel) {
                        OptionListModel model = (OptionListModel)(OptionListModel)m;
                        int size = model.getSize();
                        for (int i = 0; i < size; i++) {
                            model.removeIndexInterval(i, i);
                        }
                        BitSet selectionRange = model.getInitialSelection();
                        for (int i = 0; i < selectionRange.size(); i++) {
                            if (selectionRange.get(i)) {
                                model.addSelectionInterval(i, i);
                            }
                        }
                    } else if (m instanceof OptionComboBoxModel) {
                        OptionComboBoxModel model = (OptionComboBoxModel)(OptionComboBoxModel)m;
                        Option option = model.getInitialSelection();
                        if (option != null) {
                            model.setSelectedItem(option);
                        }
                    } else if (m instanceof JToggleButton$ToggleButtonModel) {
                        boolean checked = ((String)(String)elemAttr.getAttribute(HTML$Attribute.CHECKED) != null);
                        JToggleButton$ToggleButtonModel model = (JToggleButton$ToggleButtonModel)(JToggleButton$ToggleButtonModel)m;
                        model.setSelected(checked);
                    }
                }
            }
        }
    }
    {
    }
}
