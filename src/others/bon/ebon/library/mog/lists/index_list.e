indexing
	description: "A list of index clauses."

class
	INDEX_LIST

inherit
	MOG_LIST [INDEX_CLAUSE]
		redefine
			to_set
		end
		
creation
	make_list, make_optional_rest, make_optional_first,
	make_from_list, make_from_set
	
feature -- Conversion

	to_set: INDEX_SET is
			-- Convert `Current' into an index set.
		do
			check false end
		end
		
end -- class INDEX_LIST
