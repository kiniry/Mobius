indexing
	description: "The specification of a creation dependency between classes."

class
	CREATION_ENTRY

inherit
	ENTRY

	HASHABLE
		redefine
			is_equal
		end

creation
	make

feature -- Initialization

	make (a_creator: STRING; some_targets: CLASS_NAME_LIST) is
			-- Initialize `Current'.
		do
			create my_creator.make_from_string (a_creator)
			create my_targets.make_from_list (some_targets)
		ensure
			creator.is_equal (a_creator)
			targets.to_list.contains (some_targets)
		end

feature -- Access

	hash_code: INTEGER is
		do
			Result := my_creator.hash_code
		end

	creator: STRING is
		do
			Result := my_creator.twin
		end
	
	targets: CLASS_NAME_SET is
		do
			Result := my_targets.twin
		end

feature -- Comparison

	is_equal (other: like Current): BOOLEAN is
		do
			Result := equal (my_creator, other.my_creator) and
				equal (my_targets, other.my_targets)
		end

feature -- Element change

	set_creator (a_creator: STRING) is
		require
			a_creator /= Void
		do
			my_creator := a_creator.twin
		ensure
			creator.is_equal (a_creator)
		end

	set_targets (some_targets: CLASS_NAME_SET) is
		require
			some_targets /= Void
		do
			my_targets := some_targets.twin
		ensure
			targets.is_equal (some_targets)
		end

feature -- Removal

	wipe_out is
		do
			clear_creator
			clear_targets
		ensure then
			creator.is_empty
			targets.is_empty
		end

	clear_creator is
		do
			my_creator.wipe_out
		ensure
			creator.is_empty
		end

	clear_targets is
		do
			my_targets.wipe_out
		ensure
			targets.is_empty
		end

feature -- Output

	bon_out: STRING is
		do
			create Result.make_from_string ("creator " + my_creator.out)
			Result.append (" creates ")
			Result.append (my_targets.bon_out)
			Result.append ("%N")
		end

feature {CREATION_ENTRY} -- Implementation

	my_creator: STRING
	my_targets: CLASS_NAME_SET

invariant

	my_creator /= Void
	my_targets /= Void

end -- class CREATION_ENTRY
