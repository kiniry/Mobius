/*
 * Created on 2007-04-20
 *
 */
package umbra;

public interface IUmbraConstants {

	String SUBSTITUTE = "{1}";
	
	
	/***************************************************************************************
	 * Messages and dialog captions
	 */
	
	String DISAS_MESSAGE_TITLE =
		"Disassemble Bytecode";
	
	String B2BPL_MESSAGE_TITLE =
		"Bytecode To BoogiePL";

	String DISAS_SAVE_BYTECODE_FIRST =
		"You must save the Bytecode before you can disassemble it.";
	
	String B2BPL_SAVE_BYTECODE_FIRST =
		"You must save the Bytecode before you can translate it into BoogiePL.";

	String INVALID_EXTENSION =
		"This is not a \"" + SUBSTITUTE + "\" file.";
	
	
	/***************************************************************************************
	 * Internal strings 
	 */
	
	String BYTECODE_EDITOR_CLASS =
		"umbra.BytecodeEditor";
	
	String BOOGIEPL_EDITOR_CLASS =
		"umbra.BoogiePLEditor";

}