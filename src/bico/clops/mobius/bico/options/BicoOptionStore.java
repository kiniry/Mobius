package mobius.bico.options;

import ie.ucd.clops.runtime.options.*;

public class BicoOptionStore extends OptionStore implements BicoOptionsInterface {

  private final ie.ucd.clops.runtime.options.FileOption DirOG;
  private final ie.ucd.clops.runtime.options.FileOption OutputOG;
  private final ie.ucd.clops.runtime.options.BooleanOption MapOG;
  private final ie.ucd.clops.runtime.options.BooleanOption ListOG;
  private final ie.ucd.clops.runtime.options.BooleanOption LibOG;
  private final ie.ucd.clops.runtime.options.StringOption ClassPathOG;
  private final ie.ucd.clops.runtime.options.StringListOption ClazzOG;
  private final ie.ucd.clops.runtime.options.BooleanOption HelpOG;
  private final CLOPSErrorOption CLOPSERROROPTION;

  public BicoOptionStore() throws ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException {

    //Options
    DirOG = new ie.ucd.clops.runtime.options.FileOption("Dir","");
    addOption(DirOG);
    DirOG.setProperty("between","");
    DirOG.setProperty("allowMultiple","false");
    DirOG.setProperty("mustExist","true");
    DirOG.setProperty("mustBeDir","true");
    OutputOG = new ie.ucd.clops.runtime.options.FileOption("Output","(?:-o)");
    addOption(OutputOG);
    OutputOG.setProperty("between","");
    OutputOG.setProperty("allowMultiple","false");
    MapOG = new ie.ucd.clops.runtime.options.BooleanOption("Map","(?:-m)|(?:--map)");
    addOption(MapOG);
    ListOG = new ie.ucd.clops.runtime.options.BooleanOption("List","(?:-l)|(?:--list)");
    addOption(ListOG);
    LibOG = new ie.ucd.clops.runtime.options.BooleanOption("Lib","(?:-lib)");
    addOption(LibOG);
    ClassPathOG = new ie.ucd.clops.runtime.options.StringOption("ClassPath","(?:-cp)");
    addOption(ClassPathOG);
    ClassPathOG.setProperty("between","");
    ClassPathOG.setProperty("allowMultiple","false");
    ClazzOG = new ie.ucd.clops.runtime.options.StringListOption("Clazz","");
    addOption(ClazzOG);
    ClazzOG.setProperty("between","");
    ClazzOG.setProperty("allowMultiple","true");
    HelpOG = new ie.ucd.clops.runtime.options.BooleanOption("Help","(?:--help)");
    addOption(HelpOG);
  
    CLOPSERROROPTION = new ie.ucd.clops.runtime.options.CLOPSErrorOption();
    addOption(CLOPSERROROPTION);
  
    //Option groups
    OptionGroup OptionOG = new OptionGroup("Option");
    addOptionGroup(OptionOG);
    //Setup groupings
    OptionOG.addOptionOrGroup(HelpOG);
    OptionOG.addOptionOrGroup(LibOG);
    OptionOG.addOptionOrGroup(MapOG);
    OptionOG.addOptionOrGroup(OutputOG);
    OptionOG.addOptionOrGroup(ListOG);
    OptionOG.addOptionOrGroup(ClassPathOG);
  }
  
  public boolean isDirSet() {
    return DirOG.hasValue();
  }
  
  public java.io.File getDir() {
    return DirOG.getValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getDirOption() {
    return DirOG;
  }
  public boolean isOutputSet() {
    return OutputOG.hasValue();
  }
  
  public java.io.File getOutput() {
    return OutputOG.getValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getOutputOption() {
    return OutputOG;
  }
  public boolean isMapSet() {
    return MapOG.hasValue();
  }
  
  public boolean getMap() {
    return MapOG.getValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption getMapOption() {
    return MapOG;
  }
  public boolean isListSet() {
    return ListOG.hasValue();
  }
  
  public boolean getList() {
    return ListOG.getValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption getListOption() {
    return ListOG;
  }
  public boolean isLibSet() {
    return LibOG.hasValue();
  }
  
  public boolean getLib() {
    return LibOG.getValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption getLibOption() {
    return LibOG;
  }
  public boolean isClassPathSet() {
    return ClassPathOG.hasValue();
  }
  
  public String getClassPath() {
    return ClassPathOG.getValue();
  }
  
  public ie.ucd.clops.runtime.options.StringOption getClassPathOption() {
    return ClassPathOG;
  }
  public boolean isClazzSet() {
    return ClazzOG.hasValue();
  }
  
  public java.util.List<String> getClazz() {
    return ClazzOG.getValue();
  }
  
  public ie.ucd.clops.runtime.options.StringListOption getClazzOption() {
    return ClazzOG;
  }
  public boolean isHelpSet() {
    return HelpOG.hasValue();
  }
  
  public boolean getHelp() {
    return HelpOG.getValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption getHelpOption() {
    return HelpOG;
  }
}