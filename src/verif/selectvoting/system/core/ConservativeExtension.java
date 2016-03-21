package verif.selectvoting.system.core;

public class ConservativeExtension{
	private /*@spec_public*/ static byte[][] messages;
	/**
	 * Copies msg to messages.
	 */
	/*@
	  public normal_behaviour
	  ensures \dl_array2seq2d(messages) == \dl_array2seq2d(msg);
	  assignable messages;
	 @*/
	public static/*@helper@*/ void storeMessages(byte[][] msg){
		messages=copyOf(msg);
	}
	/**
	 * Returns a sorted copy of messages.
	 */
	/*@
	  public normal_behaviour	
	  requires messages != null;
	  requires (\forall int i; 0 <= i && i < messages.length; messages[i] != null);  
	  ensures \dl_seqPerm(\dl_array2seq2d(\result), \old(\dl_array2seq2d(messages)));
	  ensures (\forall int i; 0 <= i && i < \result.length -1 ; compare(\result[i],\result[i+1]) <= 0);
	  ensures \fresh(\result);
	  ensures (\forall int i; 0 <= i && i < messages.length; messages[i] != null);	
	  assignable \nothing;  
	@*/
	public /*@helper@*/static byte[][] retrieveSortedMessages(){
		byte[][] result = ConservativeExtension.copyOf(messages);
		sort(result, 0, result.length);
		return result;
	}
	/*@
	  public normal_behaviour
	  requires byteArrays != null;
	  requires (\forall int i; 0 <= i && i < byteArrays.length; byteArrays[i] != null);
	  requires 0 <= fromIndex && fromIndex <= byteArrays.length; 
	  requires 0 <= toIndex && toIndex <= byteArrays.length; 
	  requires fromIndex <= toIndex;
	  ensures \dl_seqPerm(\dl_array2seq(byteArrays), \old(\dl_array2seq(byteArrays)));
	  ensures (\forall int i; fromIndex <= i && i < toIndex-1; compare(byteArrays[i],byteArrays[i+1]) <= 0);	 
	  ensures (\forall int i; 0 <= i && i < byteArrays.length; byteArrays[i] != null);
	  assignable byteArrays[*];	  
	@*/
	public /*@helper@*/static void sort(byte[][] byteArrays, int fromIndex, int toIndex) {
		if (byteArrays != null) {
			if(fromIndex>=0 && toIndex<=byteArrays.length && fromIndex<toIndex){
				for(int sorted=fromIndex+1; sorted<toIndex; ++sorted){
					byte[] key = new byte[0];
					try {
						key = byteArrays[sorted]; // the item to be inserted
					} catch (Throwable t) {}
					// insert key into the sorted sequence A[fomIndex, ..., sorted-1]
					int i;
					for(i=sorted-1; i>=fromIndex; --i) {
						byte[] byteArrays_i= new byte[0];
						try {
							byteArrays_i = byteArrays[i];
						} catch (Throwable thr) {}
						if (compare(byteArrays_i, key)<=0) {
							break;
						}
						try {
							byteArrays[i+1]=byteArrays[i];
						} catch (Throwable t) {}
					}
					try {
						byteArrays[i+1]=key;
					} catch (Throwable t) {}
				}
			}
		}
	
	}
	/**
	 * KeY:
	 * We only specify the case when the result of compare is smaller or equal to 0,
	 * since this is the only way it is used in the specification and implementation 
	 * of sorting. 
	 */
	/*@
	   public normal_behaviour
	 
	   ensures  ((\exists int i; 0 <= i && i < min(a1.length, a2.length); a1[i] < a2[i] && 
	               (\forall int j; 0 <= j && j < i; a1[j] == a2[j]))
	            || 
	            ((\forall int j; 0 <= j && j < min(a1.length,a2.length); a1[j] == a2[j])
	                && a1.length <= a2.length) )   
	            <==> \result <= 0;
	            	   
	   assignable \strictly_nothing;   
	 @*/
	public /*@helper@*/static int compare(byte[] a1, byte[] a2) {
		if (a1 != null && a2 != null) {
			int n1 = a1.length;
			int n2 = a2.length;
			int m = min(n1, n2);
			/*@
			  loop_invariant 0 <=i && i <= m && n1 == a1.length && n2 == a2.length && m == min(n1, n2) &&
			                 (\forall int j; 0 <=j && j < i; a1[j] == a2[j]);
			  decreases m - i;      			  
			  assignable \strictly_nothing;
			 @*/
			for (int i = 0; i < m; i++) {
				byte b1 = -1;
				byte b2 = -1;
				try {
					b1 = a1[i];
				} catch (Throwable t) {}
				try {
					b2 = a2[i];
				} catch (Throwable t) {}
				if (b1 != b2)
					return b1 - b2;
			}
			return n1 - n2;
		}
		return 0;
	}
	/*@
	 public normal_behaviour
	 ensures  (a <= b) <==> (\result == a);
	 ensures (a > b) <==> (\result == b && a != b);
	 assignable \strictly_nothing;
	 @*/
	public /*@helper@*/static int min(int a, int b){
		if(a<=b){
			return a;
		}
		else{
			return b;
		}
	}
	/**
	 * Returns a new object which is a copy of arr.
	 */
	/*@ public normal_behaviour
	  @ requires arr != null;	  
	  @ ensures \dl_array2seq2d(\result) == \dl_array2seq2d(arr);
	  @ ensures \fresh(\result);
	  @ assignable \nothing;
	  @*/
	public /*@helper@*/static byte[][] copyOf(byte[][] arr) {
	    if (arr==null) return arr;
	    byte[][] copy = new byte[arr.length][];
	    /*@
	      loop_invariant 0 <= i && i <= arr.length 
	      && copy.length == arr.length 
	      && arr != copy && copy !=null;
	      loop_invariant (\forall int j; 0 <= j && j < i; \dl_array2seq(copy[j]) == \dl_array2seq(arr[j]));
	     
	      loop_invariant \fresh(copy);
	      loop_invariant (\forall int j; 0 <= j && j < i; copy[j] != null);
	      assignable copy[*];
	      decreases arr.length - i;
	     @*/
	    for (int i = 0; i < arr.length; i++)
	            copy[i] = copyOf(arr[i]);
	    return copy;	
	}
	
	/**
	 * Returns a new object which is a copy of message.
	 */
	/*@ public normal_behaviour
	  @ requires message != null;
	  @ ensures (\fresh(\result) && \dl_array2seq(\result) == \dl_array2seq(\old(message)));	  
	  @ assignable \nothing;
	  @*/
  public /*@helper@*/static byte[] copyOf(/*@ nullable @*/ byte[] message) {
      if (message==null) return null;
      byte[] copy = new byte[message.length];
      /*@ loop_invariant 0 <= i && i <= message.length
      @ 		&& copy != null && copy != message && \fresh(copy)
      @ 		&& copy.length == message.length
      @ 		&& (\forall int j; 0 <= j && j < i; copy[j] == message[j]);
      @ assignable copy[*];
      @ decreases message.length - i;
      @*/
      for (int i = 0; i < message.length; i++) {
          copy[i] = message[i];
      }
      return copy;
  }
	
	
}
