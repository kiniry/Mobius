indexing
	description: "A list of feature clauses."
	author: ""
	date: "$Date: 2005/05/02 22:58:30 $"
	revision: "$Revision: 1.1 $"

class
	FEATURE_CLAUSE_LIST
	
inherit
	MOG_LIST [FEATURE_CLAUSE]

creation
	make_list, make_optional_rest, make_optional_first

end -- class FEATURE_CLAUSE_LIST
