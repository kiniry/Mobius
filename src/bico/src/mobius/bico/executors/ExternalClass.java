package mobius.bico.executors;

import mobius.bico.Util;


/**
 * 
 * @author bagside
 *
 */
public class ExternalClass {
  private String path;
  private String name;
  private String bicoFileName;
  private String moduleName;
  
  public ExternalClass(String _clname) {
    String clname;
    if (_clname.endsWith(Constants.CLASS_SUFFIX)) {
    	clname = _clname.substring(0, _clname.length() - 6) ;
    } 
    else {
    	clname = _clname;
    }
    
    setModuleName(clname);
    setPath(clname);
    setName(clname);
    setBase();
  }

  private void setModuleName(String clname) {
  	moduleName = Util.coqify(clname);
  }
  
  public String getPath() {
  	return path;
  }
  
  private void setPath(String clname) {
  	int i = clname.lastIndexOf(Constants.LINUX_PATH_SEPARATOR);
    if (i == -1) {
      path = clname;
    }
    else {
      path = clname.substring(0, i);
    }
  }
  private void setName(String clname) {
  	int i = clname.lastIndexOf(Constants.LINUX_PATH_SEPARATOR);
  	name = clname.substring(i+1, clname.length());
  }
  private void setBase(){
  	String _path = path.replace(Constants.LINUX_PATH_SEPARATOR, '_');
  	bicoFileName = path + Constants.LINUX_PATH_SEPARATOR +  _path + "_" + name;
  }
  
  
  public String getTypeCoqFileName() {
  	return  getTypeName() + ".v";
  }
  
  
  public String getSignatureCoqFileName() {
  	return getSignatureName() + ".v";
  }
  
  
  public String getBicoClassCoqFileName() {
  	return getBicoClassName() + ".v";
  }
  
  public String getTypeName() {
  	return moduleName + "_type";
  }
  
  
  public String getSignatureName() {
  	return moduleName + "_signature";
  }
  
  
  public String getBicoClassName() {
  	return moduleName;
  }
  
  
  
  public String getTypeModule() {
  	return moduleName + "Type";
  }
  
  public String getSignatureModule() {
  	return moduleName + "Signature";
  }
  
  
  public String getBicoClassModule() {
  	return moduleName;
  }
  
  public String getClassName() {
  	return path + Constants.LINUX_PATH_SEPARATOR  + name + Constants.CLASS_SUFFIX;
  }
}
