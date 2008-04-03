indexing
	description: "A set of generic elements in a specification."

class
	SPECIFICATION_ELEMENTS

inherit
	MOG_SET [SPECIFICATION_ELEMENT]
	
	SPECIFICATION_ELEMENT

creation
	make, make_set, make_optional_rest, make_optional_first,
	make_from_set, make_from_list

feature -- Status report

	is_valid: BOOLEAN is
			-- A flag indicating if each of the specification elements in
			-- the the current set are valid.
		do
			Result := true
			from
				start
			until
				not after
			loop
				Result := Result and then item_for_iteration.is_valid
				forth
			end
		ensure then
			-- not Result implies exists e: SPECIFICATION_ELEMENT; has(e); not e.is_valid
		end
		
feature -- Access

	hash_code: INTEGER is
		do
			from start until off loop
				Result := Result + item_for_iteration.hash_code
			end
		end

end -- class SPECIFICATION_ELEMENTS
