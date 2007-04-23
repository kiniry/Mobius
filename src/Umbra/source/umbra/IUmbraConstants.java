/*
 * Created on 2007-04-20
 *
 */
package umbra;

public interface IUmbraConstants {

	final String SUBSTITUTE = "{1}";
	
	
	/***************************************************************************************
	 * Messages and dialog captions
	 */
	
	final String DISAS_MESSAGE_TITLE =
		"Disassemble Bytecode";
	
	final String B2BPL_MESSAGE_TITLE =
		"Bytecode To BoogiePL";

	final String DISAS_SAVE_BYTECODE_FIRST =
		"You must save the Bytecode before you can disassemble it.";
	
	final String B2BPL_SAVE_BYTECODE_FIRST =
		"You must save the Bytecode before you can translate it into BoogiePL.";

	final String INVALID_EXTENSION =
		"This is not a \"" + SUBSTITUTE + "\" file.";
	
	
	/***************************************************************************************
	 * Internal strings 
	 */
	
	final String BYTECODE_EDITOR_CLASS =
		"umbra.BytecodeEditor";
	
	final String BOOGIEPL_EDITOR_CLASS =
		"umbra.BoogiePLEditor";

}