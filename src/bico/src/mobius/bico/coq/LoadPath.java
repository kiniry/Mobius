package mobius.bico.coq;

import mobius.bico.executors.Constants;

public class LoadPath {
	private String path;
	
	public LoadPath(String _path) {
		path = _path;
	}
	
	public String print() {
		return Constants.ADD_LOAD_PATH + " \"" + path +  "\".\n"; 
	}
	
	public String toString() {
		return path;
	}
}
