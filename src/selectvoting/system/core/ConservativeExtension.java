package selectvoting.system.core;

import verif.utils.MessageTools;

public class ConservativeExtension{
	private /*@spec_public*/ static byte[][] messages;
	
	public static void storeMessages(byte[][] msg){
		messages=copyOf(msg);
	}
	
	public static byte[][] retrieveSortedMessages(){
		sort(messages, 0, messages.length);
		return messages;
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
	
	public static int compare(byte[] a1, byte[] a2) {
		if (a1 != null && a2 != null) {
			int n1 = a1.length;
			int n2 = a2.length;
			int min = min(n1, n2);
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
	
	public static int min(int n1, int n2){
		if(n1<=n2){
			return n1;
		}
		else{
			return n2;
		}
	}
	
	public static byte[][] copyOf(byte[][] arr) {
	    if (arr==null) return null;
	    byte[][] copy = new byte[arr.length][];
	    for (int i = 0; i < arr.length; i++)
	            copy[i] = MessageTools.copyOf(arr[i]);
	    return copy;	
	}
	
	
	/*@ public normal_behaviour
	  @ ensures ((\result == null) <==> (message == null))
	  @ 	&& (\result != null ==>
	  @ 		(\fresh(\result) && \result.length == message.length
	  @ 			&& \result != message
	  @ 			&& (\forall int i; 0 <= i && i < message.length;
	  @ 						\result[i] == message[i])));
	  @*/
  public static /*@ pure helper nullable @*/ byte[] copyOf(/*@ nullable @*/ byte[] message) {
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
