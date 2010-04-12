package ie.ucd.gf.impl;

import java.io.IOException;

import ie.ucd.gf.GF;
import ie.ucd.gf.GFProcess;
import ie.ucd.gf.api.GfCommands;

public class GfCommandsImpl implements GfCommands {
	
	 
	GFProcess process = GF.createPlatformSpecificProcess();
	private String output = "";

	


	@Override
	public String importLanguage(String language) throws IOException{
		
		try{
			language = language + FILE_EXTENSION;
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
