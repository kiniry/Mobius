indexing
	description: "A reference to a class by name, %
						 % possibly prefixed by one or more cluster names."

class
	STATIC_REF
	
inherit
	HASHABLE

creation
	make_ambiguous, make_from_components

feature -- Initialization

	make_ambiguous (a_string: STRING) is
			-- Initialize `Current' with the provided value.
		require
			a_string /= Void and then not a_string.is_empty
			contains_only_valid_characters (a_string)
			no_bogus_dot_placement (a_string)
		do
			my_ambiguous_value := a_string.twin
		end

	make_from_components (a_class_or_cluster_name: STRING;
												a_cluster_prefix: STRING) is
			-- Initialize `Current' with the provided values.
		require
			a_class_or_cluster_name /= Void or a_cluster_prefix /= Void
			a_class_or_cluster_name /= Void implies 
				contains_only_valid_characters (a_class_or_cluster_name) and
				not a_class_or_cluster_name.has ('.')
			a_cluster_prefix /= Void implies 
				contains_only_valid_characters (a_cluster_prefix) and
				no_bogus_dot_placement (a_cluster_prefix)
		do
			if a_class_or_cluster_name /= Void then
				create my_class_name.make_from_string (a_class_or_cluster_name)
			end
			if a_cluster_prefix /= Void then
				create my_cluster_prefix.make_from_string (a_cluster_prefix)
			end
		end

feature -- Access

	class_name: STRING is
			-- The class name of this static reference.
		do
			Result := my_class_name.twin
		end
		
	cluster_prefix: STRING is
			-- The cluster prefix of this static reference.
		do
			Result := my_cluster_prefix.twin
		end
		
	cluster (index: INTEGER): STRING is
			-- The cluster indicated by the 'index' parameter, counting from 1.
			-- Thus, the cluster prefix "com.kindsoftware.ebon" has three
			-- cluster components: at index 1, "com", at index 2, "kindsoftware",
			-- and at index 3, "ebon".  A value of Void is returned if no cluster
			-- exists at 'index'.
		require
			index > 0
		local
			dot_location: INTEGER
			ith_cluster_start_location, ith_cluster_end_location: INTEGER
			i: INTEGER
		do
			if index = 1 then
				ith_cluster_start_location := 1
				ith_cluster_end_location := index_of_dot (1)
			else
				ith_cluster_start_location := index_of_dot (index - 1)
				ith_cluster_end_location := index_of_dot (index)
			end
			if ith_cluster_start_location = 0 or ith_cluster_end_location = 0 then
				Result := Void
			else
				Result := cluster_prefix.substring (ith_cluster_start_location, ith_cluster_end_location)
			end
		ensure
			Result = Void or (cluster_prefix.has_substring (Result) and not Result.has ('.'))
		end

	hash_code: INTEGER is
		do
			if my_class_name /= Void then
				Result := my_class_name.hash_code
			end
			if my_cluster_prefix /= Void then
				Result := Result + my_cluster_prefix.hash_code
			end
			if my_ambiguous_value /= Void then
				Result := Result + my_ambiguous_value.hash_code
			end
		end

feature -- Measurement
		
	clusters_count: INTEGER is
			-- Return the number of cluster levels in this static reference.
			-- If this static reference has a class name, then the number of
			-- levels is defined as the number of dots ('.') in the cluster
			-- prefix plus one, otherwise the number of cluster levels is
			-- the number of dots in the ambiguous value, plus one.
		do
			if my_class_name /= Void then
				Result := count_dots (my_cluster_prefix) + 1
			else
				Result := count_dots (my_ambiguous_value) + 1
			end
		end

feature -- Removal

	wipe_out is
			-- Clear all values of this static reference.
		do
			clear_class_name
			clear_cluster_prefix
			clear_ambiguous_value
		end

	clear_class_name is
			-- Clear the class name of this static reference.
		do
			my_class_name := Void
		end

	clear_cluster_prefix is
			-- Clear the cluster prefix of this static reference.
		do
			my_cluster_prefix := Void
		end
		
	clear_ambiguous_value is
			-- Clear the ambiguous value of this static reference.
		do
			my_ambiguous_value := Void
		end

feature -- Transformation

	canonicalize: like Current is
		do
			Result := Current.twin
		end

feature -- Output

	bon_out: STRING is
		local
			size: INTEGER
		do
			if my_cluster_prefix /= Void then
				size := my_cluster_prefix.count
			end
			if my_class_name /= Void then
				size := size + my_class_name.count
			end
			if my_cluster_prefix /= Void and my_class_name /= Void then
				size := size + 1
			end
			create Result.make (size)
			if my_cluster_prefix /= Void then
				Result.subcopy (my_cluster_prefix, 1, my_cluster_prefix.count, 1)
			end
			if my_cluster_prefix /= Void and my_class_name /= Void then
				Result.put ('.', my_cluster_prefix.count + 1)
			end
			if my_class_name /= Void then
				Result.subcopy (my_class_name, 1, my_class_name.count,
					Result.count - my_class_name.count)
			end
		end

feature -- Status Report

	contains_only_valid_characters (a_string: STRING): BOOLEAN is
			-- Since a STATIC_REF is a concatenation of cluster names and (possibly) a
			-- class name, using the period character '.' as the glue, and cluster and
			-- class names are BON identifiers, then the only legal characters in a
			-- STATIC_REF are [a-zA-Z0-9_.]
		local
			i: INTEGER
			c: CHARACTER
		do
			Result := true
			from i := 0
			until i = a_string.count
			loop
				c := a_string @ i
				if not (c.is_alpha or c.is_digit or c = '.') then
					Result := false
				end
			end
		end
		
	no_bogus_dot_placement (a_string: STRING): BOOLEAN is
			-- A cluster prefix must not start with a dot, nor can it end with a
			-- dot, nor can two dots be adjacent.
		do
			Result := true
			if a_string @ 1 = '.' or a_string @ a_string.count = '.' then
				Result := false
			end
			if a_string.has_substring ("..") then
				Result := false
			end
		end

	valid_static_reference: BOOLEAN is
			-- Since a STATIC_REF is a concatenation of cluster names and (possibly) a
			-- class name, using the period character '.' as the glue, and cluster and
			-- class names are BON identifiers, then the only legal characters in a
			-- STATIC_REF are [a-zA-Z0-9_.]
		do
			Result := true
			if my_class_name /= Void then
				Result := Result and contains_only_valid_characters (my_class_name)
			end
			if my_cluster_prefix /= Void then
				Result := Result and contains_only_valid_characters (my_cluster_prefix) and
					no_bogus_dot_placement (my_cluster_prefix)
			end
			if my_ambiguous_value /= Void then
				Result := Result and contains_only_valid_characters (my_ambiguous_value) and
					no_bogus_dot_placement (my_cluster_prefix)
			end
		end

feature {STATIC_REF} -- Implementation

	count_dots (a_string: STRING): INTEGER is
			-- Returns the number of dots in the passed string.
		require
			a_string /= Void and then not a_string.is_empty
			contains_only_valid_characters (a_string)
			no_bogus_dot_placement (a_string)
		local
			index: INTEGER
			count: INTEGER
		do
			from count := 0; index := 1
			until index = 0
			loop
				-- Starting from an index of 2 is fine because a_string cannot start
				-- with a dot anyway due to the invariants of STATIC_REF.
				index := a_string.index_of ('.', index + 1)
				if index /= 0 then
					count := count + 1
				end
			end
			Result := count
			ensure
				Result >= 0
		end
		
	index_of_dot (d: INTEGER): INTEGER is
			-- The index into cluster_prefix of the dth "dot" (period, '.'),
			-- or 0 if there is no such dot.
			-- E.g., the cluster prefix of "com.kindsoftware.ebon" would have
			-- index_of_dot (1) = 4 and index_of_dot (2) = 17.  For all other
			-- positive values of d > 2, index_of_dot(d) = 0.
		local
			i, start, location: INTEGER
		do
			if cluster_prefix /= Void then
				from i := 0; start := 1; location := 1
				until i = d or location = 0
				loop
					location := cluster_prefix.index_of ('.', start)
					start := location + 1
				end
				Result := location
			else
				Result := 0
			end
		end

	my_class_name: STRING
	my_cluster_prefix: STRING
	my_ambiguous_value: STRING

invariant

--	my_ambiguous_value /= Void xor (my_class_name /= Void or my_cluster_prefix /= Void)
	my_class_name /= Void implies not my_class_name.is_empty
	my_class_name /= Void implies not my_class_name.has ('.')
	my_cluster_prefix /= Void implies not my_cluster_prefix.is_empty
	my_ambiguous_value /= Void implies my_class_name = Void and my_cluster_prefix = Void
	my_ambiguous_value /= Void implies not my_ambiguous_value.is_empty
	valid_static_reference

end -- class STATIC_REF
