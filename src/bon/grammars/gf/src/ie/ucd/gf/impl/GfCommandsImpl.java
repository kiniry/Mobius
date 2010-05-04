package ie.ucd.gf.impl;

import java.io.IOException;
import java.util.ResourceBundle;
import java.util.MissingResourceException;

import ie.ucd.gf.FileUtil;
import ie.ucd.gf.GF;
import ie.ucd.gf.GFProcess;
import ie.ucd.gf.api.GfCommands;

/**
 * @author Aidan
 *
 */
public class GfCommandsImpl implements GfCommands {
	
	private String output = "";
	private String filesLocation = "";
	public final static String PARSE_FROM = "p -lang=";
	public final static String LINEARIZE_TO = " | l -lang=";
	public final static String FILE_EXTENSION = ".gfo";
	public final static String IMPORT = "i ";
	public final static String LINKING = "linking ... OK";
	
	boolean gfFilesexported = FileUtil.copyGFSourceFiles();
	GFProcess process = GF.createPlatformSpecificProcess();
	
	


	@Override
	public String importLanguage(String language) throws IOException{
		
		try{
			filesLocation = FileUtil.getGFFileDirectory();
			language = filesLocation + language + FILE_EXTENSION;
			output = process.importLanguage(IMPORT + language);
			
		}catch (IOException e) {
			System.out.println("Unable to import Language: "+language+": "+e.getMessage());
		}
		return output;

		
	}

	@Override
	public String translateSentence(String languageFrom, String languageTo,
			String sentence) {
		try{
			sentence = " \"" + sentence + "\""; //add quotes to the sentence
			output = process.enterCommand(PARSE_FROM + languageFrom +  sentence + LINEARIZE_TO + languageTo);
		} catch (IOException e) {
			System.out.println("Unable to process sentence: "+sentence+": "+e.getMessage());
		}
		return output;
	}

	

	public boolean ProcessIsAlive(){
		return process.isAlive();
	}

	/* (non-Javadoc)
	 * @see ie.ucd.gf.api.GfCommands#quitProcess()
	 */
	@Override
	public void quitProcess() throws IOException {
		process.quitProcess();
		
	}







}
