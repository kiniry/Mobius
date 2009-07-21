indexing
	description: "A generic element of a specification."

deferred class
	SPECIFICATION_ELEMENT

inherit
	ANY
		undefine
			copy, is_equal
		end

	BON_TEXT

	CANONICALIZABLE

	HASHABLE
		undefine
			copy, is_equal
		end

feature -- Status report

	is_valid: BOOLEAN is
			-- A flag indicating if the current element is valid.
		deferred
		end

end -- class SPECIFICATION_ELEMENT
