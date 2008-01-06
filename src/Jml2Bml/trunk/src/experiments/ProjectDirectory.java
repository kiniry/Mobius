package experiments;

import java.io.File;
import java.io.IOException;

public class ProjectDirectory {
	public static final String PROJECT_DIR = getCurrentDir(); 
	
	private static String getCurrentDir(){
		File dir1 = new File (".");
		try {
			System.out.println ("Current dir : " + dir1.getCanonicalPath());
			return dir1.getCanonicalPath();
		} catch (IOException e) {
			e.printStackTrace();
			return "Error";
		}
	}
}
