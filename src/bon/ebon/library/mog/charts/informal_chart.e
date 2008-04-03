indexing
	description: "A generic chart."

deferred class
	INFORMAL_CHART

inherit
	PART_SEMANTICS

	SPECIFICATION_ELEMENT

feature {NONE} -- Initialization

	make_informal_chart (a_name: STRING; 
											 an_index: INDEX_LIST;
											 an_explanation: STRING; 
											 a_part: STRING) is
			-- Initialize `Current'.
		require
			a_name /= Void
			an_explanation /= Void
			a_part /= Void
		do
			create my_name.make_from_string (a_name)
			create my_index.make_from_list (an_index)
			create my_explanation.make_from_string (an_explanation)
			create my_part.make_from_string (a_part)
		ensure
			name.is_equal (a_name)
			index.is_equal (an_index)
			explanation.is_equal (an_explanation)
			part.is_equal (a_part)
		end

feature -- Duplication

	copy (other: like Current) is
		do
			set_name (other.name)
			set_index (other.index)
			set_explanation (other.explanation)
			set_part (other.part)
		end

feature -- Access

	hash_code: INTEGER is
		do
			Result := my_name.hash_code + my_explanation.hash_code + my_part.hash_code
		end

	name: STRING is
			-- The name of this chart.
		do
			Result := my_name.twin
		ensure
			Result /= Void
		end

	index: INDEX_LIST is
			-- The index list of this chart.
		do
			Result := my_index.twin
		ensure
			Result /= Void
		end

	explanation: STRING is
			-- The explanation for this chart.
		do
			Result := my_explanation.twin
		ensure
			Result /= Void
		end

	part: STRING is
			-- The part number of this chart.
		do
			Result := my_part.twin
		ensure
			Result /= Void
		end

feature -- Measurement

	index_count: INTEGER is
			-- The number of index terms of this chart.
		do
			Result := my_index.count
		ensure
			Result >= 0
		end

feature -- Status report

	is_valid: BOOLEAN is
			-- A valid informal chart has a non-trivial name.
		do
			Result := not name.is_empty
		ensure then
			Result = not name.is_empty
		end

	is_part_of (other: like Current): BOOLEAN is
			-- An informal chart C is a part of another informal chart D iff
			-- C's index is a part of D's index and C's explanation is a part
			-- of D's explanation.  C and D's name and part are not considered.
		do
			Result := index.is_part_of (other.index) and
				other.explanation.has_substring (Current.explanation)
		end

	contains (other: like Current): BOOLEAN is
		do
			Result := index.contains (other.my_index) and
				explanation.has_substring (other.explanation)
		end

	is_disjoint (other: like Current): BOOLEAN is
		do
			Result := not is_part_of (other) and not other.is_part_of (Current)
		end

feature -- Comparison

	is_equal (other: like Current): BOOLEAN is
		do
			Result := my_name.is_equal (other.my_name) and
				my_index.is_equal (other.my_index) and
				my_explanation.is_equal (other.my_explanation) and
				my_part.is_equal (other.my_part)
		end

feature -- Element change

	set_name (a_name: STRING) is
		require
			a_name /= Void
		do
			my_name := a_name.twin
		ensure
			name.is_equal (a_name)
		end

	set_index (an_index: INDEX_LIST) is
		do
			my_index := an_index.twin
		ensure
			index.is_equal (an_index)
		end

	set_explanation (an_explanation: STRING) is
		require
			an_explanation /= Void
		do
			my_explanation := an_explanation.twin
		ensure
			explanation.is_equal (an_explanation)
		end

	set_part (a_part: STRING) is
		require
			a_part /= Void
		do
			my_part := a_part.twin
		ensure
			part.is_equal (a_part)
		end

	add_index_clause (a_clause: INDEX_CLAUSE) is
		do
			my_index.put_last (a_clause)
		ensure
			index.has (a_clause)
		end

feature -- Removal

	wipe_out is
			-- Remove all contents.
		do
			clear_name
			clear_index
			clear_explanation
			clear_part
		ensure
			name.is_empty
			index.is_empty
			explanation.is_empty
			part.is_empty
		end

	clear_name is
		do
			my_name.wipe_out
		ensure
			name.is_empty
		end

	clear_index is
		do
			my_index.wipe_out
		ensure
			index.is_empty
		end

	clear_explanation is
		do
			my_explanation.wipe_out
		ensure
			explanation.is_empty
		end

	clear_part is
		do
			my_part.wipe_out
		ensure
			part.is_empty
		end

feature -- Transformation

	canonicalize: like Current is
			-- The canonical form of an informal chart is:
			--   a. duplicate properties are eliminated from the index list, and
			--   b. the resulting reduced index list is canonicalized
			-- No changes are made to the informal chart's name, explanation, or
			-- part.
		do
			Result := Current.twin
			Result.set_index (my_index.canonicalize)
		end

feature -- Output

	bon_out: STRING is
		require else
			is_valid
		do
			create Result.make_from_string ("indexing%N")
			Result.append (my_index.bon_out)
			Result.append ("explanation%N")
			Result.append (my_explanation.out)
			Result.append ("part %"" + my_part.out + "%"%N")
		end

feature -- Basic operations

	merge (other: like Current): like Current is
			-- Merge indices of two charts.  Likewise for other basic operations.
		do
			my_index := my_index.merge (other.my_index.twin)
		end

	intersect (other: like Current): like Current is
		do
			my_index := my_index.intersect (other.my_index)
		end

	subtract (other: like Current): like Current is
		do
			my_index := my_index.subtract (other.my_index)
		end

	symdif (other: like Current): like Current is
		do
			my_index := my_index.symdif (other.my_index.twin)
		end

feature {INFORMAL_CHART} -- Implementation

	my_name: STRING
	my_index: INDEX_LIST
	my_explanation: STRING
	my_part: STRING

invariant

	name /= Void
	index /= Void
	explanation /= Void
	part /= Void

end -- class INFORMAL_CHART
