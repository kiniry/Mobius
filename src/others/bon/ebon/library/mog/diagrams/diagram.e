indexing
	description: "A generic diagram."

deferred class
	DIAGRAM

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

	PART_SEMANTICS

end -- class DIAGRAM
