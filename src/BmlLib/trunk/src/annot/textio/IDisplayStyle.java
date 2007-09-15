package annot.textio;

public interface IDisplayStyle {

	public static boolean goControlPrint = false;
	public static int max_total_line_width = 60;
	public static final boolean go3argQuantifiers = true;
	
	public static final boolean goShowRightMargin = true;

	public static final String comment_start = "/* ";
	public static final String comment_next = " * ";
	public static final String comment_end = " */";
	public static final int comment_length = comment_next.length();

	public static final char expr_block_start = '{';
	public static final char expr_block_end = '}';
	public static final String lineIndent = "  ";

	public static final String jt_int = "int";
	public static final String jt_boolean = "boolean";

	public static final String __mspec = "method specification";
	public static final String __classInvariant = "class invariant";
	public static final String __assertTable = "assert table";
	public static final String __second_cp = "second constant pool";

	public static final String _classInvariant = "\\class invariant";
	public static final String _assert = "\\assert";
	public static final String _requires = "\\requires ";
	public static final String _sc_start = "{|";
	public static final String _sc_end = "|}";
	public static final String _precondition = "\\precondition";
	public static final String _postcondition = "\\ensures";

}
