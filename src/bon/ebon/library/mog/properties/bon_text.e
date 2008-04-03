indexing
	description: "An entity that has a printable representation in the %
							% BON textual format."

deferred class
	BON_TEXT

inherit
	ANY
		undefine
			copy, is_equal
		end

feature -- Output

	bon_out: STRING is
			-- Return a printable representation of `Current' in the BON
			-- textual format.
		deferred
		ensure
			Result /= Void
		end

end -- class BON_TEXT
