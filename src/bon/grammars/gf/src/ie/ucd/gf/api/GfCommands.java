package ie.ucd.gf.api;

import java.io.IOException;

public interface GfCommands {
	
	public String translateSentence(String languageFrom, String languageTo, String Sentence);
		
	public String importLanguage(String language)throws IOException;
	
	public void quitProcess()throws IOException;
	
	public boolean ProcessIsAlive();
		

}
