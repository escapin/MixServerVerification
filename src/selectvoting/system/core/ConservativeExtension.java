package selectvoting.system.core;

import de.unitrier.infsec.utils.MessageTools;

public class ConservativeExtension{
	private static byte[][] messages;
	
	public static void storeMessages(byte[][] msg){
		messages=MessageTools.copyOf(msg);
	}
	
	public static byte[][] retrieveSortedMessages(){
		sort(messages, 0, messages.length);
		return messages;
	}
	
	private static void sort(byte[][] byteArrays, int fromIndex, int toIndex) {	
		if(fromIndex>=0 && toIndex<=byteArrays.length && fromIndex<toIndex){
			for(int sorted=fromIndex+1; sorted<toIndex; ++sorted){
				byte[] key=byteArrays[sorted]; // the item to be inserted
				// insert key into the sorted sequence A[fomIndex, ..., sorted-1]
				int i;
				for(i=sorted-1; i>=fromIndex && Utils.compare(byteArrays[i], key)>0; --i)
					byteArrays[i+1]=byteArrays[i];
				byteArrays[i+1]=key;
			}	
		}
	}	
}
