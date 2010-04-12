package ie.ucd.gf.api;

import java.io.IOException;

public interface GfCommands {
	
	
	public String translateSentence(String languageFrom, String languageTo, String Sentence);
		
	public String importLanguage(String language)throws IOException;
	
	public void quitProcess()throws IOException;
	
	public boolean ProcessIsAlive();
	
	public final static String PARSE_FROM = "p -lang=";
	
	public final static String LINEARIZE_TO = " | l -lang=";
	
	public final static String FILE_EXTENSION = ".gfo";
	
	public final static String IMPORT = "i ";
	
	public final static String LINKING = "linking ... OK";
	
	
	

}
