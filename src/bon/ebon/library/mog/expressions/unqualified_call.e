indexing
	description: "Objects that ..."
	author: ""
	date: "$Date: 2005/05/02 22:58:31 $"
	revision: "$Revision: 1.1 $"

class
	UNQUALIFIED_CALL

inherit
	HASHABLE

feature -- Access

	hash_code: INTEGER is
		do
			check false end
		end

end -- class UNQUALIFIED_CALL
