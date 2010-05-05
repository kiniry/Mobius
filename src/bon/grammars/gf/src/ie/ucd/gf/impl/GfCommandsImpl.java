package ie.ucd.gf.impl;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
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
	public final static String PARSE_FROM_FORMAL = "p -lang=FormalBON";
	public final static String LINEARIZE_TO_INFORMAL = " | l -lang=InformalBON | ps -unlextext";
	public final static String PARSE_FROM_INFORMAL = "ps -lextext ";
	public final static String LINEARIZE_TO_FORMAL = " | p -lang=InformalBON | l -lang=FormalBON";
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
	public String translateSentenceFromFormalBON(String sentence) {
		try{
			sentence = " \"" + sentence + "\""; //add quotes to the sentence
			output = process.enterCommand(PARSE_FROM_FORMAL +  sentence + LINEARIZE_TO_INFORMAL);
		} catch (IOException e) {
			System.out.println("Unable to process sentence: "+sentence+": "+e.getMessage());
		}
		return output;
	}
	
	@Override
	public String translateSentenceToFormalBON(String sentence) {
		try{
			sentence = " \"" + sentence + "\""; //add quotes to the sentence
			output = process.enterCommand(PARSE_FROM_INFORMAL + sentence + LINEARIZE_TO_FORMAL);
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

	/* (non-Javadoc)
	 * @see ie.ucd.gf.api.GfCommands#translateQueryToFormalBON(java.lang.String)
	 */
	@Override
	public Map translateQueryToFormalBON(String sentence) {
		String returned = translateSentenceToFormalBON(sentence);
		int colon = returned.indexOf(":");
		String name = returned.substring(0, colon);
		String value = returned.substring(colon + 1);
		Map<String,Object> m = new HashMap<String,Object>();
		m.put(name,value);
		return m;
	}







}
