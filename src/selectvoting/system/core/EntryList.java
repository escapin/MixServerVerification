package selectvoting.system.core;


public class EntryList {

        /*@ spec_public @*/ static class Node
		{
			public /*@ nullable @*/ byte[] entry;
			public /*@ nullable @*/ Node next;

			/*@ public normal_behaviour
	          @ requires true;
	          @ assignable this.entry, this.next;
	          @ ensures this.entry == entry && this.next == null;
	          @*/
			public Node(/*@ nullable @*/ byte[] entry)
			{
				this.entry = entry;
				this.next=null;
			}
		}

		private /*@ spec_public nullable @*/ Node head, last;
		private int size;


		public EntryList(){
			head=last=null;
			size=0;
		}

		/*@ public normal_behaviour
	      @ requires head == null;
	      @ assignable head, last;
	      @ ensures head != null && last != null
	      @     && head.entry == entry && last.entry == entry
	      @     && \fresh(head) && \fresh(last);
	      @ also
	      @ public normal_behaviour
	      @ requires head != null && last != null;
	      @ assignable last, last.next;
	      @ ensures last != null && last.entry == entry && \fresh(last);
	      @ also
	      @ public exceptional_behaviour
	      @ requires head != null && last == null;
	      @ diverges true;
	      @ signals_only NullPointerException;
	      @ assignable \nothing;
	      @ signals (NullPointerException e) true;
	      @*/
		public /*@ helper @*/ void add(/*@ nullable @*/ byte[] entry)
		{
			Node newEntry=new Node(entry);
			if(head==null)
				head=last=newEntry;
			else {
				Node tmp = last;
				if (last == tmp && tmp != null) {
					tmp.next = newEntry;
				}
				last = tmp;
			}
			size++;
		}

		public int size(){
			return size;
		}

		/*@ public behaviour
	      @ requires true;
	      @ diverges true;
	      @ signals_only NullPointerException;
	      @ ensures true;
	      @ signals (NullPointerException e) true;
	      @*/
		public /*@ pure helper nullable @*/ void toArray(byte[][] arr)
		{
			int i=0;
			Node tmp = head;

			/*@ loop_invariant head != null;
              @ assignable entries;
              @*/
			while (tmp != null) {
				byte[] x = tmp.entry;
				try {
					arr[i] = x;
				} catch (Throwable t) {}
				i++;
				tmp = tmp.next;
			}
		}		
}