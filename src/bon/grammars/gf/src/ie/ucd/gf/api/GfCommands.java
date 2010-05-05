package ie.ucd.gf.api;

import java.io.IOException;
import java.util.Map;

public interface GfCommands {
	
	public String translateSentenceFromFormalBON(String Sentence);
	
	public String translateSentenceToFormalBON(String Sentence);
	
	public Map translateQueryToFormalBON(String Sentence);
		
	public String importLanguage(String language)throws IOException;
	
	public void quitProcess()throws IOException;
	
	public boolean ProcessIsAlive();
		

}
