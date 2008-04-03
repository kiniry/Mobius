indexing
	description: "A list of class invariants."

class
	INVARIANT_LIST

inherit
	MOG_LIST [CLASS_INVARIANT]
		redefine
			to_set
		end
		
creation
	make_list, make_optional_rest, make_optional_first,
	make_from_list, make_from_set
	
feature -- Conversion

	to_set: INVARIANT_SET is
			-- Convert `Current' into a class invariant set.
		do
			check false end
		end

end -- class INVARIANT_LIST
