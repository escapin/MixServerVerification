package verif.selectvoting.system.core;

import verif.utils.MessageTools;

public class Utils 
{
	public static byte[] concatenateMessageArrayWithDuplicateElimination(byte[][] messages) {
		return concatenateMessageArray(messages, messages.length);
	}
	
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


	public static byte[] concatenateMessageArray(byte[][] messages, int len) {
		byte[] msg = new byte[0];
		for (int i=len-1; i>=0; --i) { // from the last to the first
			msg = MessageTools.concatenate(messages[i], msg);
		}
		return msg;
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
	
	/**
	 * Compares its two array arguments for lexicographic order. 
	 * 
	 * @param a1 the first array to be compared.
	 * @param a2 the second array to be compared.
	 * @return a negative integer, zero, or a positive integer as the first argument is 
	 * 			less than, equal to, or greater than the second
	 */
	/*@
	   
	 @*/
	public static int compare(byte[] a1, byte[] a2) {
		if (a1 != null && a2 != null) {
			int n1 = a1.length;
			int n2 = a2.length;
			int min = Math.min(n1, n2);
			for (int i = 0; i < min; i++) {
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
	  requires byteArrays != null;
	  requires 0 <= fromIndex && fromIndex < byteArrays.length; 
	  requires 0 <= toIndex && toIndex < byteArrays.length; 
	  requires fromIndex <= toIndex;
	  ensures \dl_seqPerm(\dl_array2seq(byteArrays), \old(\dl_array2seq(byteArrays)));
	  ensures (\forall int i; fromIndex <= i && i < toIndex; compare(byteArrays[i],byteArrays[i+1]) <= 0);	  
	@*/
	public static void sort(byte[][] byteArrays, int fromIndex, int toIndex) {
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
						if (Utils.compare(byteArrays_i, key)<=0) {
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
	
	public static byte[][] copyOf(byte[][] arr) {
	    if (arr==null) return null;
	    byte[][] copy = new byte[arr.length][];
	    for (int i = 0; i < arr.length; i++)
	            copy[i] = MessageTools.copyOf(arr[i]);
	    return copy;	
	}	
		
}