indexing
	description: "A list of types."
	author: "Joseph Kiniry <kiniry@kindsoftware.com>"
	date: "$Date: 2005/12/21 14:06:18 $"
	revision: "$Revision: 1.2 $"

class
	ACTUAL_GENERICS

inherit
	MOG_LIST [BON_TYPE]
		redefine
			bon_out
		end

creation
	make_uniform_list, make_list, make_optional_rest, make_optional_first,
	make_from_list

feature -- Output

	bon_out: STRING is
		do
			Result := "[ "
			Result.append (Precursor)
			Result.append (" ]")
		end

invariant

	not is_empty

end -- class ACTUAL_GENERICS
