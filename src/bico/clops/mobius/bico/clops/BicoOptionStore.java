package mobius.bico.clops;

import ie.ucd.clops.runtime.options.CLOPSErrorOption;
import ie.ucd.clops.runtime.options.OptionGroup;
import ie.ucd.clops.runtime.options.OptionStore;

public class BicoOptionStore extends OptionStore implements BicoOptionsInterface {

  private final ie.ucd.clops.runtime.options.BooleanOption HelpOG;
  private final ie.ucd.clops.runtime.options.FileOption DirOG;
  private final ie.ucd.clops.runtime.options.StringListOption ClazzOG;
  private final ie.ucd.clops.runtime.options.FileOption OutputOG;
  private final ie.ucd.clops.runtime.options.BooleanOption MapOG;
  private final ie.ucd.clops.runtime.options.BooleanOption ListOG;
  private final ie.ucd.clops.runtime.options.BooleanOption LibOG;
  private final ie.ucd.clops.runtime.options.StringOption ClassPathOG;
  private final CLOPSErrorOption CLOPSERROROPTION;

  public BicoOptionStore() throws ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException {

    //Options
    HelpOG = new ie.ucd.clops.runtime.options.BooleanOption("Help", "(?:-h)|(?:--help)");
    addOption(HelpOG);
    HelpOG.setProperty("description", "Show the help message.");
    DirOG = new ie.ucd.clops.runtime.options.FileOption("Dir", "");
    addOption(DirOG);
    DirOG.setProperty("between", "");
    DirOG.setProperty("mustExist", "true");
    DirOG.setProperty("mustBeDir", "true");
    DirOG.setProperty("description", 
      "Specify directory in which Bico does its job (there must" +
      "be only one directory, and this argument is mandatory).");
    ClazzOG = new ie.ucd.clops.runtime.options.StringListOption("Clazz", "");
    addOption(ClazzOG);
    ClazzOG.setProperty("suffixregexp", "([a-zA-Z.]+)\0");
    ClazzOG.setProperty("description", 
      "Generates also the file for the specified classes, bico must be able" +
      "to find them in its class path.");
    OutputOG = new ie.ucd.clops.runtime.options.FileOption("Output", "(?:-o)");
    addOption(OutputOG);
    OutputOG.setProperty("description", "Used to specify the output directory.");
    MapOG = new ie.ucd.clops.runtime.options.BooleanOption("Map", "(?:-m)|(?:--map)");
    addOption(MapOG);
    MapOG.setProperty("description", "Triggers the generation of the map implementation.");
    ListOG = new ie.ucd.clops.runtime.options.BooleanOption("List", "(?:-l)|(?:--list)");
    addOption(ListOG);
    ListOG.setProperty("description", "Triggers the generation of the list implementation.");
    LibOG = new ie.ucd.clops.runtime.options.BooleanOption("Lib", "(?:-lib)");
    addOption(LibOG);
    LibOG.setProperty("description", 
      "Enables the java.lang library generation." +
      "It implies the generation of most of the JRE.");
    ClassPathOG = new ie.ucd.clops.runtime.options.StringOption("ClassPath", "(?:-cp)");
    addOption(ClassPathOG);
    ClassPathOG.setProperty("description", "Specifies the base working class path.");
  
    CLOPSERROROPTION = new ie.ucd.clops.runtime.options.CLOPSErrorOption();
    addOption(CLOPSERROROPTION);
  
    //Option groups
    final OptionGroup MainOG = new OptionGroup("Main");
    addOptionGroup(MainOG);
    final OptionGroup TypeOG = new OptionGroup("Type");
    addOptionGroup(TypeOG);
    final OptionGroup MiscOG = new OptionGroup("Misc");
    addOptionGroup(MiscOG);
    //Setup groupings
    MainOG.addOptionOrGroup(DirOG);
    MainOG.addOptionOrGroup(ClazzOG);
    TypeOG.addOptionOrGroup(MapOG);
    TypeOG.addOptionOrGroup(ListOG);
    MiscOG.addOptionOrGroup(LibOG);
    MiscOG.addOptionOrGroup(OutputOG);
    MiscOG.addOptionOrGroup(ClassPathOG);
  }
  
 /* Option Help.
  * Description: Show the help message.
  * Aliases: [-h, --help]
  */
  
  /**
   * {@inheritDoc}
   */
  public boolean isHelpSet() {
    return HelpOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public boolean getHelp() {
    return HelpOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public boolean getRawHelp() {
    return HelpOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption getHelpOption() {
    return HelpOG;
  }
  
 /* Option Dir.
  * Description: Specify directory in which Bico does its job (there must 
  		   be only one directory, and this argument is mandatory).
  * Aliases: []
  */
  
  /**
   * {@inheritDoc}
   */
  public boolean isDirSet() {
    return DirOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public java.io.File getDir() {
    return DirOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public java.io.File getRawDir() {
    return DirOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getDirOption() {
    return DirOG;
  }
  
 /* Option Clazz.
  * Description: Generates also the file for the specified classes, bico must be able 
           to find them in its class path.
  * Aliases: []
  */
  
  /**
   * {@inheritDoc}
   */
  public boolean isClazzSet() {
    return ClazzOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public java.util.List<String> getClazz() {
    return ClazzOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public java.util.List<String> getRawClazz() {
    return ClazzOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.StringListOption getClazzOption() {
    return ClazzOG;
  }
  
 /* Option Output.
  * Description: Used to specify the output directory.
  * Aliases: [-o]
  */
  
  /**
   * {@inheritDoc}
   */
  public boolean isOutputSet() {
    return OutputOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public java.io.File getOutput() {
    return OutputOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public java.io.File getRawOutput() {
    return OutputOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getOutputOption() {
    return OutputOG;
  }
  
 /* Option Map.
  * Description: Triggers the generation of the map implementation.
  * Aliases: [-m, --map]
  */
  
  /**
   * {@inheritDoc}
   */
  public boolean isMapSet() {
    return MapOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public boolean getMap() {
    return MapOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public boolean getRawMap() {
    return MapOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption getMapOption() {
    return MapOG;
  }
  
 /* Option List.
  * Description: Triggers the generation of the list implementation.
  * Aliases: [-l, --list]
  */
  
  /**
   * {@inheritDoc}
   */
  public boolean isListSet() {
    return ListOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public boolean getList() {
    return ListOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public boolean getRawList() {
    return ListOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption getListOption() {
    return ListOG;
  }
  
 /* Option Lib.
  * Description: Enables the java.lang library generation. 
 		   It implies the generation of most of the JRE.
  * Aliases: [-lib]
  */
  
  /**
   * {@inheritDoc}
   */
  public boolean isLibSet() {
    return LibOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public boolean getLib() {
    return LibOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public boolean getRawLib() {
    return LibOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption getLibOption() {
    return LibOG;
  }
  
 /* Option ClassPath.
  * Description: Specifies the base working class path.
  * Aliases: [-cp]
  */
  
  /**
   * {@inheritDoc}
   */
  public boolean isClassPathSet() {
    return ClassPathOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public String getClassPath() {
    return ClassPathOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public String getRawClassPath() {
    return ClassPathOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.StringOption getClassPathOption() {
    return ClassPathOG;
  }
  
}
