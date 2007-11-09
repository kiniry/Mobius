package mobius.bico.executors;


/**
 * 
 * @author bagside
 *
 */
public class ExternalClass {
	private String path;
	private String name;
	private String bicoFileName;
	
	public ExternalClass(String _clname) {
		String clname;
		if (_clname.endsWith(Constants.CLASS_SUFFIX)) {
			clname = _clname.substring(0, _clname.length() - 6) ;
		} else {
			clname = _clname;
		}
		setPath(clname);
		setName(clname);
		setBase();
	}

	public String getPath() {
		return path;
	}

	private void setPath(String clname) {
		int i = clname.lastIndexOf(Constants.LINUX_PATH_SEPARATOR);
		path = clname.substring(0, i);
	}
	private void setName(String clname) {
		int i = clname.lastIndexOf(Constants.LINUX_PATH_SEPARATOR);
		name = clname.substring(i+1, clname.length());
	}
	private void setBase(){
		String _path = path.replace(Constants.LINUX_PATH_SEPARATOR, '_');
		bicoFileName = path +Constants.LINUX_PATH_SEPARATOR +  _path + "_" + name;
	}

	
	public String getTypeName() {
		return bicoFileName + "_type.v";
	}
	
	
	public String getSignatureName() {
		return bicoFileName + "_signature.v";
	}
	

	public String getBicoClassName() {
		return bicoFileName + ".v";
	}
	
	public String getClassName() {
	   return path + Constants.LINUX_PATH_SEPARATOR  + name + Constants.CLASS_SUFFIX;
	}
	
	
}
