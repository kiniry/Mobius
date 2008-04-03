indexing
	description: "An indefinite or definite reference to a (possibly %
							% indirectly parameterized) class."

class
	INDIRECTION_ELEMENT
	
inherit
	HASHABLE
	
	ELIDED

creation
	make, make_ellipses

feature -- Initialization

	make (a_named_indirection: NAMED_INDIRECTION) is
		require
			a_named_indirection /= Void
		do
			my_named_indirection := a_named_indirection.twin
		ensure
			named_indirection.is_equal (a_named_indirection)
		end

feature -- Access

	named_indirection: NAMED_INDIRECTION is
			-- The named indirection of this indirection element, or `Void' if
			-- one has not been set.
		do
			Result := my_named_indirection.twin
		end

	hash_code: INTEGER is
		do
			if my_named_indirection /= Void then
				Result := my_named_indirection.hash_code
			else
				Result := 0
			end
		end

feature {INDIRECTION_ELEMENT} -- Implementation

	my_named_indirection: NAMED_INDIRECTION

end -- class INDIRECTION_ELEMENT
