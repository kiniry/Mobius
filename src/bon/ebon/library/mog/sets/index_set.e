indexing
	description: "A set of index clauses."

class
	INDEX_SET

inherit
	MOG_SET [INDEX_CLAUSE]
		redefine
			to_list
		end

creation
	make, make_set, make_optional_rest, make_optional_first,
	make_from_set, make_from_list

feature -- Conversion

	to_list: INDEX_LIST is
			-- Convert `Current' into an index list.
		do
			check false end
		end
		
end -- class INDEX_SET
