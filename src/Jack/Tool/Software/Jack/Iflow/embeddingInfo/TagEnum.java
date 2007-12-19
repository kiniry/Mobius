package embeddingInfo;
/*
 * Created on Jan 17, 2005
 * @version $Id: TagEnum.java,v 1.2 2005/03/21 09:36:38 lmartini Exp $
 */

/**
 * @author Luca Martini
 *
 */

import javax.print.attribute.EnumSyntax;

public class TagEnum extends EnumSyntax {
    public static final TagEnum START_CLASS = new TagEnum(0);
    public static final TagEnum END_CLASS = new TagEnum(1);
    public static final TagEnum START_METHOD = new TagEnum(2);
    public static final TagEnum END_METHOD = new TagEnum(3);
    public static final TagEnum COMMENT = new TagEnum(4);
    public static final TagEnum FIELD = new TagEnum(5);
    public static final TagEnum HEAP_EFFECT = new TagEnum(6);
    public static final TagEnum EXC_EFFECT = new TagEnum(7);
    public static final TagEnum REGISTER = new TagEnum(8);
    public static final TagEnum RETURN = new TagEnum(9);
    public static final TagEnum IMPLICIT = new TagEnum(10);
    public static final TagEnum EXCSAFE = new TagEnum(11);

    private static final String[] stringTable = {
	"@class",
	"@endclass",
	"@method",
	"@endmethod",
	"@comment",
	"@field",
	"@heapeffect",
	"@exceffect",
	"@register",
	"@return",
	"@implicit",
	"@exceptionsafe"
    };

    protected String[] getStringTable() {
	return stringTable;
    }
    
    private static final TagEnum[] enumValueTable = {
	START_CLASS,
	END_CLASS,
	START_METHOD,
	END_METHOD,
	COMMENT,
	FIELD,
	HEAP_EFFECT,
	EXC_EFFECT,
	REGISTER,
	RETURN,
	IMPLICIT,
	EXCSAFE
    };
    
    protected EnumSyntax[] getEnumValueTable() {
	return enumValueTable;
    }
    
    protected TagEnum(int i) {
	super(i);
    }
    
    public static TagEnum search(String s) {
	for (int i=0;i<stringTable.length;i++)
	    if (s.equals(stringTable[i]))
		return enumValueTable[i];
	return null;
    }
}    
