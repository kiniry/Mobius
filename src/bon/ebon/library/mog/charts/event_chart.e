indexing
	description: "A event chart."

class
	EVENT_CHART
	
	-- Used direct access to attributes in this class as an experiment in design.

inherit
	INFORMAL_CHART
		redefine
			bon_out,
			canonicalize,
			copy, is_equal,
			is_part_of, contains, is_disjoint,
			merge, intersect, subtract, symdif,
			wipe_out
		end

creation
	make

feature -- Initialization

	make (a_name: STRING; 
				a_classifier: STRING;
				an_index: INDEX_LIST;
				an_explanation: STRING; 
				a_part: STRING; 
				some_entries: EVENT_ENTRIES) is
			-- Initialize `Current'.
		require
			a_name /= Void
			valid_classifier (a_classifier)
			an_explanation /= Void
			a_part /= Void
		local
			temp: STRING
		do
			make_informal_chart (a_name, an_index, an_explanation, a_part)
			create my_entries.make_from_set (some_entries)
			create temp.make_from_string (a_classifier)
			temp.to_upper
			if (temp /= Void) then
				if temp.is_equal ("INCOMING") then
					set_incoming
				else
					set_outgoing
				end
			end
			set_entries (some_entries)
		ensure
			entries.is_equal (some_entries)
			a_classifier.as_upper.is_equal ("INCOMING") implies incoming
			not a_classifier.as_upper.is_equal ("INCOMING") implies outgoing
		end

feature -- Access

	incoming: BOOLEAN is
		do
			Result := my_classifier.is_equal ("INCOMING")
		end

	outgoing: BOOLEAN is
		do
			Result := my_classifier.is_equal ("OUTGOING")
		end

	unclassified: BOOLEAN is
		do
			Result := my_classifier = Void
		end

	entries: EVENT_ENTRIES is
		do
			Result := my_entries.twin
		ensure
			non_void_result: Result /= Void
		end

feature -- Measurement

	entries_count: INTEGER is
		do
			Result := my_entries.count
		ensure
			non_negative_result: Result >= 0
		end

feature -- Duplication

	copy (other: like Current) is
		do
			Precursor (other)
			set_entries (other.my_entries)
			if other.incoming then set_incoming
			else if other.outgoing then set_outgoing
					 else unclassify
					 end
			end
		end

feature -- Status report

	valid_classifier (a_classifier: STRING): BOOLEAN is
		local
			temp: STRING
		do
			create temp.make_from_string (a_classifier)
			temp.to_upper

			Result := temp /= Void implies 
			  (temp.is_equal ("INCOMING") or temp.is_equal ("OUTGOING"))
		end

	is_part_of (other: like Current): BOOLEAN is
		do
			Result := Precursor (other) and
				incoming = other.incoming and
				entries.is_part_of (other.my_entries)
		end

	contains (other: like Current): BOOLEAN is
		do
			Result := Precursor (other) and
				incoming = other.incoming and
				entries.contains (other.my_entries)
		end

	is_disjoint (other: like Current): BOOLEAN is
		do
			Result := Precursor (other) and
				incoming /= other.incoming and
				entries.is_disjoint (other.my_entries)
		end

feature -- Comparison

	is_equal (other: like Current): BOOLEAN is
		do
			Result := Precursor (other) and 
				my_classifier.is_equal (other.my_classifier) and
				my_entries.is_equal (other.my_entries)
		end

feature -- Element change

	set_incoming is
		do
			my_classifier := "INCOMING"
		end

	set_outgoing is
		do
			my_classifier := "OUTGOING"
		end

	unclassify is
		do
			my_classifier := Void
		end

	set_entries (some_entries: EVENT_ENTRIES) is
		do
			my_entries := some_entries.twin
		ensure
			entries.is_equal (some_entries)
		end

	add_entries (some_entries: EVENT_ENTRIES) is
		do
			my_entries := my_entries.merge (some_entries)
		ensure
			some_entries.is_part_of (entries)
			entries_count = entries.merge (some_entries).count
		end

	add_entry (an_entry: EVENT_ENTRY) is
		do
			my_entries.put (an_entry)
		ensure
			entries.has (an_entry)
			not (old entries).has (an_entry) implies entries_count = old entries_count + 1
			(old entries).has (an_entry) implies entries_count = old entries_count
		end

feature -- Removal

	wipe_out is
			-- Remove all contents.
		do
			Precursor
			unclassify
			clear_entries
		ensure then
			entries.is_empty
		end

	clear_entries is
		do
			my_entries.wipe_out
		ensure
			entries.is_empty
		end

	remove_entries (some_entries: EVENT_ENTRIES) is
		do
			my_entries := my_entries.subtract (some_entries)
		ensure
			entries.is_disjoint (some_entries)
			entries_count = old entries_count - entries.intersect (some_entries).count
		end

	remove_entry (an_entry: EVENT_ENTRY) is
		do
			my_entries.remove (an_entry)
		ensure
			not entries.has (an_entry)
			old entries.has (an_entry) implies entries_count = old entries_count - 1
			not old entries.has (an_entry) implies entries_count = old entries_count
		end

feature -- Transformation

	canonicalize: like Current is
		local
			informal_chart: INFORMAL_CHART
		do
			informal_chart := Precursor
			create Result.make (informal_chart.name, my_classifier, informal_chart.index, 
				informal_chart.explanation, informal_chart.part, Void)
			Result.set_entries (entries.canonicalize)
		end

feature -- Output

	bon_out: STRING is
		do
			create Result.make_from_string ("event_chart " + my_name + "%N")
			if incoming then
				Result.append ("incoming%N")
			else
				Result.append ("outgoing%N")
			end
			Result.append (Precursor)
			Result.append (entries.bon_out)
			Result.append ("end%N")
		end

feature -- Basic operations

	merge (other: like Current): like Current is
			-- If the charts being merged have the same classification, then the resulting
			-- chart has that classification; otherwise, the result is unclassified.
		local
			informal_chart: INFORMAL_CHART
		do
			informal_chart := Precursor (other)
			create Result.make (informal_chart.name, Void, informal_chart.index, 
				informal_chart.explanation, informal_chart.part, Void)
			Result.set_entries (entries.merge (other.my_entries))
			if incoming and other.incoming then
				Result.set_incoming
			else if outgoing and other.outgoing then
						 Result.set_outgoing
					 else Result.unclassify
					 end	
			end
		ensure then
			incoming_classification: incoming and other.incoming implies Result.incoming
			outgoing_classification: outgoing and other.outgoing implies Result.outgoing
			unclassified_classification: not (incoming and other.incoming) or not (outgoing and other.outgoing) implies
				Result.unclassified
		end

	intersect (other: like Current): like Current is
			-- If the charts being intersected have the same classification, then the resulting
			-- chart has that classification; otherwise, the result is unclassified.
		local
			informal_chart: INFORMAL_CHART
		do
			informal_chart := Precursor (other)
			create Result.make (informal_chart.name, Void, informal_chart.index, 
				informal_chart.explanation, informal_chart.part, Void)
			Result.set_entries (entries.intersect (other.my_entries))
			if incoming and other.incoming then
				Result.set_incoming
			else if outgoing and other.outgoing then
						 Result.set_outgoing
					 else Result.unclassify
					 end	
			end
		ensure then
			incoming_classification: incoming and other.incoming implies Result.incoming
			outgoing_classification: outgoing and other.outgoing implies Result.outgoing
			unclassified_classification: not (incoming and other.incoming) or not (outgoing and other.outgoing) implies
				Result.unclassified
		end

	subtract (other: like Current): like Current is
			-- If the charts being subtracted have the same classification, then the resulting
			-- chart has that classification; otherwise, the result is unclassified.
		local
			informal_chart: INFORMAL_CHART
		do
			informal_chart := Precursor (other)
			create Result.make (informal_chart.name, Void, informal_chart.index, 
				informal_chart.explanation, informal_chart.part, Void)
			Result.set_entries (entries.subtract (other.my_entries))
			if incoming and other.incoming then
				Result.set_incoming
			else if outgoing and other.outgoing then
						 Result.set_outgoing
					 else Result.unclassify
					 end	
			end
		ensure then
			incoming_classification: incoming and other.incoming implies Result.incoming
			outgoing_classification: outgoing and other.outgoing implies Result.outgoing
			unclassified_classification: not (incoming and other.incoming) or not (outgoing and other.outgoing) implies
				Result.unclassified
		end

	symdif (other: like Current): like Current is
			-- If the charts being symdiffed have the same classification, then the resulting
			-- chart has no classification; otherwise, the result has the classification of `Current'.
		local
			informal_chart: INFORMAL_CHART
		do
			informal_chart := Precursor (other)
			create Result.make (informal_chart.name, Void, informal_chart.index, 
				informal_chart.explanation, informal_chart.part, Void)
			Result.set_entries (entries.symdif (other.my_entries))
			if incoming and other.incoming then
				Result.unclassify
			else if outgoing and other.outgoing then
						 Result.unclassify
					 else if incoming then
									Result.set_incoming
								else if outgoing then
											 Result.set_outgoing
										 else Result.unclassify
										 end
								end
					 end
			end
		ensure then
			incoming_classification: incoming and other.incoming implies Result.unclassified
			outgoing_classification: outgoing and other.outgoing implies Result.unclassified
			unclassified_classification: not (incoming and other.incoming) or not (outgoing and other.outgoing) implies
				outgoing = Result.outgoing and incoming = Result.incoming and unclassified = Result.unclassified
		end

feature {EVENT_CHART} -- Implementation

	my_classifier: STRING
	my_entries: EVENT_ENTRIES

invariant
	
	my_classifier /= Void implies 
		my_classifier.is_equal ("INCOMING") xor my_classifier.is_equal ("OUTGOING")
	my_entries /= Void
	unclassified xor incoming xor outgoing

end -- class EVENT_CHART
