package ie.ucd.autograder.config;

import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;

public class FloatFieldEditor extends StringFieldEditor {

  public static final int DEFAULT_TEXT_LIMIT = 5;

  private float minValidValue = Float.MIN_VALUE;
  private float maxValidValue = Float.MAX_VALUE;
  private boolean rangeSet;

  public FloatFieldEditor(String name, String labelText, Composite parent) {
    this(name, labelText, parent, DEFAULT_TEXT_LIMIT);
  }

  public FloatFieldEditor(String name, String labelText, Composite parent, int textWidth) {
    init(name, labelText);
    rangeSet = false;
    setTextLimit(textWidth);
    setEmptyStringAllowed(false);
    setErrorMessage("Not a valid float number.");
    createControl(parent);
  }

  /**
   * Sets the range of valid values for this field.
   * 
   * @param min the minimum allowed value (inclusive)
   * @param max the maximum allowed value (inclusive)
   */
  public void setValidRange(float min, float max) {
    minValidValue = min;
    maxValidValue = max;
    rangeSet = true;
    setErrorMessage("Not a valid float number in the range " + min + "-" + max + ".");
  }

  /* (non-Javadoc)
   * Method declared on StringFieldEditor.
   * Checks whether the entered String is a valid float or not.
   */
  protected boolean checkState() {

    Text text = getTextControl();
    if (text == null) {
      return false;
    }

    String numberString = text.getText();
    try {
      float number = Float.valueOf(numberString).floatValue();
      if (!rangeSet || (number >= minValidValue && number <= maxValidValue)) {
        clearErrorMessage();
        return true;
      } else {
        showErrorMessage();
        return false;
      }
    } catch (NumberFormatException e1) {
      showErrorMessage();
      return false;
    }
  }

  /* (non-Javadoc)
   * Method declared on FieldEditor.
   */
  protected void doLoad() {
    Text text = getTextControl();
    if (text != null) {
      float value = getPreferenceStore().getFloat(getPreferenceName());
      text.setText("" + value);//$NON-NLS-1$
      oldValue = "" + value; //$NON-NLS-1$
    }

  }

  /* (non-Javadoc)
   * Method declared on FieldEditor.
   */
  protected void doLoadDefault() {
    Text text = getTextControl();
    if (text != null) {
      float value = getPreferenceStore().getDefaultFloat(getPreferenceName());
      text.setText("" + value);//$NON-NLS-1$
    }
    valueChanged();
  }

  /* (non-Javadoc)
   * Method declared on FieldEditor.
   */
  protected void doStore() {
    Text text = getTextControl();
    if (text != null) {
      Float f = new Float(text.getText());
      getPreferenceStore().setValue(getPreferenceName(), f.floatValue());
    }
  }

  /**
   * Returns this field editor's current value as a float.
   *
   * @return the value
   * @exception NumberFormatException if the <code>String</code> does not
   *   contain a parsable float
   */
  public float getFloatValue() throws NumberFormatException {
    return new Float(getStringValue()).floatValue();
  }

}
