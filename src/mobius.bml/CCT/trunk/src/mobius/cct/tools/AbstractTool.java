package mobius.cct.tools;

import java.text.MessageFormat;
import java.util.ResourceBundle;

/**
 * Abstract tool with some utility methods.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public abstract class AbstractTool implements Tool {
  /**
   * Localized messages.
   */
  private ResourceBundle fMessages;
  
  /**
   * Load localized messages.
   * @param env Environment.
   */
  private void loadMessages(final Environment env) {
    if (fMessages == null) {
      fMessages = Main.getMessages(getClass(), env.getLocale());
    }
  }
  
  /**
   * Get localized message.
   * @param key Key.
   * @param e Environment.
   * @param args Message arguments.
   * @return Message.
   */
  protected String getMessage(final String key, 
                              final Environment e,
                              final Object... args) {
    loadMessages(e);
    final MessageFormat fmt = 
      new MessageFormat(fMessages.getString(key), e.getLocale());
    return fmt.format(args);
  }
  
  /**
   * Get tool description.
   * @param env Environment;
   * @return Description.
   */
  public String getDescription(final Environment env) {
    return getMessage("tool.description", env);
  }
  
}
