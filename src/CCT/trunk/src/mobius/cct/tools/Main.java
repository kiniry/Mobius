package mobius.cct.tools;

import java.text.MessageFormat;
import java.util.HashMap;
import java.util.Locale;
import java.util.Map;
import java.util.ResourceBundle;

import mobius.cct.tools.add.AddTool;
import mobius.cct.tools.extract.ExtractTool;
import mobius.cct.tools.help.HelpTool;
import mobius.cct.tools.info.InfoTool;
import mobius.cct.tools.merge.MergeTool;

/**
 * Main class.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class Main {
  /**
   * Constructor.
   */
  private Main() {
  }
  
  /**
   * Load localized messages for given class.
   * Messages should be stored in the same folder as
   * the class file, in file Messages.properties .
   * @param cls Class.
   * @param l Locale.
   * @return Resource bundle with localized messages.
   */
  public static ResourceBundle getMessages(final Class<?> cls,
                                           final Locale l) {
    final String dir = 
      cls.getPackage().getName().replace('.', '/');
    return ResourceBundle.getBundle(dir + "/" + 
                                    "Messages", l);
  }
  
  /**
   * Entry point.
   * First argument is interpreted as a name of a tool.
   * @param args Command line arguments.
   */
  public static void main(final String[] args) {
    final Environment env = new DefaultEnvironment(args);
    final ResourceBundle messages = 
      getMessages(Main.class, env.getLocale());
    final Map<String, Tool> tools = getTools();  
    
    if (args.length == 0) {
      System.err.println(messages.getString("main.usage"));
    } else {
      final String toolName = args[0];
      if (tools.containsKey(toolName)) {
        final Tool tool = tools.get(toolName);
        tool.main(env);
      } else {
        final String msg = 
          messages.getString("main.error.unknown.tool");
        final MessageFormat fmt = 
          new MessageFormat(msg, env.getLocale());
        System.err.println(
          fmt.format(new Object[]{toolName})
        );
      }
    } 
  }

  /**
   * Get list of tools.
   * @return Tools.
   */
  private static Map<String, Tool> getTools() {
    final Map<String, Tool> result = 
      new HashMap<String, Tool>();
    
    result.put("info", new InfoTool());
    result.put("add", new AddTool());
    result.put("extract", new ExtractTool());
    result.put("merge", new MergeTool());
    result.put("help", new HelpTool(result)); 
    
    return result;
  }
  
}
