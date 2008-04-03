indexing
	description: "A list of class types."
	author: "Joseph Kiniry <kiniry@kindsoftware.com>"
	date: "$Date: 2005/05/02 22:58:30 $"
	revision: "$Revision: 1.1 $"

class
	CLASS_TYPE_LIST

inherit
	MOG_LIST [CLASS_TYPE]

creation
	make_list, make_optional_rest, make_optional_first, make_from_linear
	
end -- class CLASS_TYPE_LIST
