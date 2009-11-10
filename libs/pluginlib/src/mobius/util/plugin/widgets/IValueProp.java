package mobius.util.plugin.widgets;

public interface IValueProp {

  /**
   * Sets the value to the built-in default value.
   */
  void setDefault();
  
  
  /**
   * Sets the value of the associated option based on the
   * current UI setting.
   */
  void setOptionValue();
}
