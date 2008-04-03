indexing
	description: "A set of queries."

class
	QUERY_SET

inherit
	STRING_SET
		redefine
			to_list
		end

creation
	make_set, make_optional_rest, make_optional_first,
	make_from_set, make_from_list,
  make_from_string_set

feature -- Conversion

	to_list: QUERY_LIST is
			-- Convert `Current' into a query list.
		do
			check false end
		end
		
end -- class QUERY_SET
