package verif.selectvoting.system.core;

import verif.utils.MessageTools;

public class Utils 
{
//	public static byte[] concatenateMessageArrayWithDuplicateElimination(byte[][] messages) {
//		return concatenateMessageArray(messages, messages.length);
//	}
	
	// we assume messages[][] is sorted
	public static byte[] concatenateMessageArrayWithDuplicateElimination(byte[][] messages, int len) {
		byte[] msg = new byte[0];
		byte[] last = null;
		for (int i=len-1; i>=0; --i) { // from the last to the first
			byte[] current = messages[i];
			if (last==null || !MessageTools.equal(current, last)) {
				msg = MessageTools.concatenate(current, msg);
			}
			last = current;
		}
		return msg;
	}


//	public static byte[] concatenateMessageArray(byte[][] messages, int len) {
//		byte[] msg = new byte[0];
//		for (int i=len-1; i>=0; --i) { // from the last to the first
//		    try {
//			msg = MessageTools.concatenate(messages[i], msg);
//		    } catch (Throwable t) {}
//		}
//		return msg;
//	}
	
	public static byte[] concatenateMessageArray(int i, byte[][] messages){
		try{
			
			if(i == messages.length){
				return new byte[0];
			}
			else{
				return MessageTools.concatenate(messages[i], concatenateMessageArray(i+1, messages));
			}
			
		}catch(Throwable t){}
		return new byte[0];
	}

	public static class MessageSplitIter {
		byte[] rest;

		public MessageSplitIter(byte[] message) {
			rest = message;
		}
		public boolean notEmpty() {
			return rest.length>0;
		}
		public byte[] current() {
			return MessageTools.first(rest);
		}
		public void next() {
			if (notEmpty()) 
				rest = MessageTools.second(rest);
		}
	}

	/*@
	 public normal_behaviour
	 ensures  (a <= b) <==> (\result == a);
	 ensures (a > b) <==> (\result == b && a != b);
	 assignable \strictly_nothing;
	 @*/
	public /*@helper@*/static int min(int a, int b){
		if(a <= b){
			return a;
		}
		return b;
	}
	

	
	/**
	 * Compares its two array arguments for lexicographic order. 
	 * 
	 * @param a1 the first array to be compared.
	 * @param a2 the second array to be compared.
	 * @return a negative integer, zero, or a positive integer as the first argument is 
	 * 			less than, equal to, or greater than the second
	 */

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

				/*@
				  loop_invariant (\forall int i; fromIndex <= i && i < sorted-1; compare(byteArrays[i],byteArrays[i+1]) <= 0);
				  
				  loop_invariant 0 <= fromIndex && fromIndex <= byteArrays.length;
				  loop_invariant 0 <= toIndex && toIndex <= byteArrays.length;
				  loop_invariant fromIndex <= toIndex;
				  loop_invariant fromIndex <= sorted && sorted <= toIndex;
				  
				  loop_invariant \dl_seqPerm(\dl_array2seq(byteArrays), \old(\dl_array2seq(byteArrays)));
				  loop_invariant byteArrays != null && (\forall int i; 0 <= i && i < byteArrays.length; byteArrays[i]!=null);
				  assignable byteArrays[sorted..toIndex];
				  decreases toIndex - sorted;
				  @*/
				for(int sorted=fromIndex; sorted<toIndex; ++sorted){
					selSort(byteArrays, fromIndex, sorted);

				}
			}
		}	
	}
	/*@
	  public normal_behaviour
	  requires 0 <= fromIndex && fromIndex <= byteArrays.length;
	  requires 0 <= sorted && sorted < byteArrays.length;
	  requires (\forall int i; 0 <= i && i < byteArrays.length; byteArrays[i] != null);
	  requires fromIndex <= sorted;
	  requires (\forall int i; fromIndex <= i && i < sorted-1; compare(byteArrays[i],byteArrays[i+1]) <= 0);
	  ensures  (\forall int i; fromIndex <= i && i < sorted; compare(byteArrays[i],byteArrays[i+1]) <= 0);
	  ensures   \dl_seqPerm(\dl_array2seq(byteArrays), \old(\dl_array2seq(byteArrays)));
	  ensures (\forall int i; 0 <= i && i < byteArrays.length; byteArrays[i] != null);
	  assignable byteArrays[fromIndex..sorted];	  
	@*/	
	private /*@helper@*/static void selSort(byte[][] byteArrays, int fromIndex, int sorted) {		
		try {
			byte[] key = byteArrays[sorted]; // the item to be inserted
			int i = shiftRight(byteArrays, fromIndex, sorted, key);
			byteArrays[i]=key;
		} catch (Throwable t) {}		
	}	
	
	/*@
    public normal_behaviour
    requires 0 <= fromIndex && fromIndex <= byteArrays.length;
    requires 0 <= sorted && sorted < byteArrays.length;
    requires fromIndex <= sorted; 
    requires key == byteArrays[sorted];   
    ensures (\forall int i; fromIndex <= i && i <= \result; byteArrays[i] == \old(byteArrays[i]));
    ensures (\forall int i; \result < i && i <= sorted; byteArrays[i] == \old(byteArrays[i-1]));    
    ensures fromIndex <= \result && \result <=sorted; 
    ensures fromIndex < \result ==> compare(byteArrays[\result - 1], key) <= 0;
    ensures \result < sorted ==> compare(key, byteArrays[\result + 1]) <= 0;    
    assignable byteArrays[fromIndex..sorted];
    @*/
	private static/*@helper@*/ int shiftRight(byte[][] byteArrays, int fromIndex, int sorted, byte[] key) {
		int i;
		/*@
		 loop_invariant i <= sorted-1 && i >= fromIndex - 1;
		 loop_invariant (\forall int j; i + 2 <= j && j <= sorted;  byteArrays[j] == \old(byteArrays[j-1]));
		 loop_invariant (\forall int j; fromIndex <= j && j <= i+1;  byteArrays[j] == \old(byteArrays[j]));                 
		 loop_invariant (\forall int j; i + 1 <= j && j <= sorted; compare(key, byteArrays[j]) <= 0 );                
		 assignable byteArrays[fromIndex..sorted]; 
		 decreases i+1;
		 @*/
		for(i=sorted-1; i>=fromIndex; --i) {
			//byte[] byteArrays_i= new byte[0];
			try {				
				if (Utils.compare(byteArrays[i], key)<=0) {
					break;
				}
				byteArrays[i+1]=byteArrays[i];
			} catch (Throwable thr) {}			
			
		}
		return i+1;
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
		/**
		 * We cannot say 'if (arr==null) return null' here. Here is why:
		 * Some compilers (e.g. the Oracle JDK 1.8.0_45) generate code
		 * which performs a redundant checked cast of null to byte[][]
		 * before null is returned.
		 * Joana (or WALA respectively) does not perform any additional
		 * class cast analysis and hence conservatively assumes that the
		 * checked cast operation may fail with an exception.
		 * This appears to cause several violations. The reason for that has
		 * not been investigated yet.
		 * Interestingly, Eclipse's compiler does not generate this cast. So
		 * it could be easy to integrate this optimization into WALA to overcome
		 * this problem.
		 */
	    if (arr==null) return arr;
	    byte[][] copy = new byte[arr.length][];;
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
	    for (int i = 0; i < arr.length; i++){
//	    	copy[i] = arr[i];
	    	try {
	            copy[i] = MessageTools.copyOf(arr[i]);
	        } catch (Throwable t) {}
	    }
	    return copy;	
	}	
		
}