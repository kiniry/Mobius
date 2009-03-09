package mobius.bico.options;

public interface BicoOptionsInterface {

  public boolean isDirSet();
  
  public java.io.File getDir();
  
  public boolean isOutputSet();
  
  public java.io.File getOutput();
  
  public boolean isMapSet();
  
  public boolean getMap();
  
  public boolean isListSet();
  
  public boolean getList();
  
  public boolean isLibSet();
  
  public boolean getLib();
  
  public boolean isClassPathSet();
  
  public String getClassPath();
  
  public boolean isClazzSet();
  
  public java.util.List<String> getClazz();
  
  public boolean isHelpSet();
  
  public boolean getHelp();
  
}