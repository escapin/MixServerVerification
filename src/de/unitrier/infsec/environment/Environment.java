package de.unitrier.infsec.environment;

class NodeValue {
	int value;
	NodeValue next;
	NodeValue(int v, NodeValue n) {
		value = v; next = n;
	}
}

class NodeList {
	public static class Node {
		public /*@ nullable @*/ String entry;
		public /*@ nullable @*/ Node next;

		/*@ public normal_behaviour
          @ requires true;
          @ assignable this.entry, this.next;
          @ ensures this.entry == entry && this.next == null;
          @*/
		public Node(/*@ nullable @*/ String entry) {
			this.entry = entry;
			this.next=null;
		}
	}

	public /*@ spec_public nullable @*/ Node head, last;

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
	public /*@ helper @*/ void add(/*@ nullable @*/ String entry) {
		Node newEntry=new Node(entry);
		if(head==null)
			head=last=newEntry;
		else {
			last.next=newEntry;
			last=newEntry;
		}
	}
}

public class Environment {

	private /*@ spec_public @*/ static boolean result; // the LOW variable
	
	private /*@ spec_public @*/ static NodeValue listValue = null;
	private /*@ spec_public @*/ static boolean listInitializedValue = false;

	private static NodeValue initialValue() {
		// Unknown specification of the following form:
		// return new Node(U1, new Node(U2, ...));
		// where U1, U2, ...Un are constant integers.
		return new NodeValue(1, new NodeValue(7,null));  // just an example
	}

	/*@ public behaviour
      @ assignable inputCounter;
      @ diverges true;
      @ ensures true;
      @*/
	public static /*@ helper @*/ int untrustedInput() {
    	if (!listInitializedValue) {
    		listValue = initialValue();
    	    listInitializedValue = true;        
    	}
    	if (listValue==null) return 0;
    	int tmp = listValue.value;
    	listValue = listValue.next;
    	return tmp;
	}

	/*@ public behaviour
      @ diverges true;
      @ assignable inputCounter, result;
      @ ensures true;
      @*/
    public static /*@ helper @*/ void untrustedOutput(int x) {
		if (untrustedInput()!=0) {
			result = (x==untrustedInput());
			throw new Error();  // abort
		}
	}

    /*@ public behaviour
      @ diverges true;
      @ assignable inputCounter;
      @ ensures true;
      @*/
    public static /*@ helper nullable @*/ byte[] untrustedInputMessage() {
		int len = untrustedInput();
		if (len<0) return null;
		byte[] returnval = new byte[len];

		/*@ loop_invariant true;
          @ assignable inputCounter, returnval[*];
          @*/
		for (int i = 0; i < len; i++)
			returnval[i] = (byte) untrustedInput();
		return returnval;    
    }

    /*@ public behaviour
      @ diverges true;
      @ assignable inputCounter, result;
      @ ensures true;
      @*/
    public static /*@ helper @*/ void untrustedOutputMessage(/*@ nullable @*/ byte[] t) {
    	untrustedOutput(t.length);

        /*@ loop_invariant true;
          @ assignable inputCounter, result;
          @*/
		for (int i = 0; i < t.length; i++) {
			untrustedOutput(t[i]);
		}
    }

	private static NodeList stringsList = null;

	public static String untrustedInputString() {
		int choice = untrustedInput();
		if(choice==1){ // return a new string
    		int l=untrustedInput();
    		String s="";
    		for(int i=0; i<l; i++)
    			s += (char) untrustedInput();
    		if(stringsList==null)
    			stringsList = new NodeList();
    		stringsList.add(s);
    		return s;
		} else if (choice==2){ // return a string previously exchanged
    		if(stringsList==null)
    			return "";
    		for(NodeList.Node node=stringsList.head; node!=null; node=node.next)	
    			if(untrustedInput()!=0)
    				return node.entry;
    	}
		return "";
    }

	/*@ public behaviour
      @ diverges true;
      @ assignable inputCounter, result;
      @ ensures true;
      @*/
    public static /*@ helper @*/ void untrustedOutputString(String s) {
    	if(stringsList==null)
    		stringsList = new NodeList();
    	// value comparison
    	untrustedOutput(s.length());

        /*@ loop_invariant true;
          @ assignable inputCounter, result;
          @*/
    	for (int i = 0; i < s.length(); i++)
        	untrustedOutput(s.charAt(i));
    	// reference comparison
    	for(NodeList.Node node=stringsList.head; node!=null; node=node.next)
    		untrustedOutput(s==node.entry ? 1:0);
    	stringsList.add(s);
    }
}
