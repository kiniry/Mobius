indexing
	description: "A generic indirection consisting of either a formal generic %
							% name or a named indirection."

class GENERIC_INDIRECTION

inherit
	ANY

	BON_TEXT
	
	HASHABLE

creation
	make_direct, make_indirect
	
feature -- Initialization

	make_direct (a_formal_generic_name: STRING) is
			-- 
		require
			a_formal_generic_name /= Void and then not a_formal_generic_name.is_empty
		do
			my_formal_generic_name := a_formal_generic_name.twin
		ensure
			formal_generic_name.is_equal (a_formal_generic_name)
		end
		
	make_indirect (a_named_indirection: NAMED_INDIRECTION) is
			-- 
		require
			a_named_indirection /= Void
		do
			my_named_indirection := a_named_indirection.twin
		ensure
			named_indirection.is_equal (a_named_indirection)
		end

feature -- Access

	formal_generic_name: STRING is
			-- The formal generic name of this generic indirection, or `Void' if
			-- one has not been specified.
		do
			Result := my_formal_generic_name.twin
		ensure
			Result = Void or else not Result.is_empty
		end

	named_indirection: NAMED_INDIRECTION is
			-- The named indirection of this generic indirection, or `Void' if
			-- one has not been specified.
		do
			Result := my_named_indirection.twin
		end

	hash_code: INTEGER is
		do
			if my_formal_generic_name /= Void then
				Result := my_formal_generic_name.hash_code
			else
				Result := my_named_indirection.hash_code
			end
		end
		
feature -- Output

	bon_out: STRING is
		do
			if my_formal_generic_name /= Void then
				Result := my_formal_generic_name.out
			else
				Result := my_named_indirection.bon_out
			end
		end

feature {GENERIC_INDIRECTION} -- Implementation

	my_formal_generic_name: STRING
	my_named_indirection: NAMED_INDIRECTION

invariant
	(my_formal_generic_name /= Void and then not my_formal_generic_name.is_empty) xor
	my_named_indirection /= Void

end -- class GENERIC_INDIRECTION
