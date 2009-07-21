indexing
	description: "A list of queries."

class
	QUERY_LIST

inherit
	STRING_LIST
		redefine
			to_set
		end

creation
	make, make_optional_rest, make_optional_first, make_from_list,
	make_from_string_list

feature -- Conversion

	to_set: QUERY_SET is
			-- Convert `Current' into a query set.
		do
			check false end
		end

end -- class QUERY_LIST
