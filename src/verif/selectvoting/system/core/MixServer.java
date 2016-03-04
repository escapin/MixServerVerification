package verif.selectvoting.system.core;

import verif.selectvoting.system.core.Utils.MessageSplitIter;
import verif.functionalities.pkienc.Decryptor;
import verif.functionalities.pkienc.Encryptor;
import verif.functionalities.pkisig.Signer;
import verif.functionalities.pkisig.Verifier;
import verif.utils.MessageTools;

public class MixServer 
{	
	// Cryptographic functionalities
	private final Signer signer;
	private final Decryptor decryptor;
	private final Verifier precServVerif;
	private final byte[] electionID;
	// private final int numberOfVoters;

	 

	// PUBLIC CLASSES
	/**
	 * Error thrown if the input data is ill-formed.
	 */

	public static class MalformedData extends Exception {
		public int errCode;
		public String description;
		public MalformedData(int errCode, String description) {
			this.errCode = errCode;
			this.description = description;
		}
		public String toString() {
			return "Mix Server Error: " + description;
		}
	}

	public static class ServerMisbehavior extends Exception {
		public int errCode;
		public String description;
		public ServerMisbehavior(int errCode, String description) {
			this.errCode = errCode;
			this.description = description;
		}
		public String toString() {
			return "Previous Server Misbehavior: " + description;
		}
	}

	// CONSTRUCTORS

	public MixServer(Decryptor decryptor, Signer signer, Verifier precServVerif, byte[] electionID) {
		this.signer = signer;
		this.decryptor = decryptor;
		this.electionID = electionID;
		this.precServVerif = precServVerif;
	}
	
	

	// this is the randomly chosen message array
	//@ public ghost instance byte[][] msg;
	// this is the value of entr_arr after the call to Utils.sort
	//@ public ghost instance byte[][] a;
	// this is the value of entr_arr after the call to ConservativeExtenson.getRandomMessages
	//@ public ghost instance byte[][] b;


	// PUBLIC METHODS

	/**
	 * Process data that supposed to be the signed output of the preceding mix server. 
	 * Returns the signed result of the mixing. 
	 * 
	 * I/O format:
	 * 			SIGN_prec[tag, elID, ballotsAsAMessage]
	 * where, each ballot:
	 * 			ENC_curr[elID, innerBallot] 
	 * 
	 */
	/*
	 * Assuming that the messages stored in the CE are a permutation of msg we prove
	 * That the values in entr_arr after sort() are equal to the values of entr_arr after 
	 * ConservativeExtension.retrieveSortetMessages().
	 */
	/*@
	  requires \dl_seqPerm(\dl_array2seq(msg), \dl_array2seq(ConservativeExtension.messages)); 	  
	  ensures a.length == b.length && (\forall int i; 0 <= i && i < a.length; a[i] == b[i]);
	 @*/	
	public byte[] processBallots(byte[] data) throws MalformedData, ServerMisbehavior {

		


		byte[] ballotsAsAMessage = checkAndGetBallots(data);

		byte[][] entr_arr = extractBallots(ballotsAsAMessage);


		/**
		 * Assumption: the messages in the array variable 'entr_arr' above 
		 * are a permutation of the messages in the array variable 'msg' in Setup.java
		 * 
		 * Assumption necessary because of the issues in verifying that the 
		 * encryption scheme works:
		 * The property 
		 * 	'The message decrypted is equals to the message previously 
		 * 	 encrypted' 
		 * is too demanding and time consuming for KeY.
		 */


		entr_arr = sort(entr_arr); 
		//@set a = entr_arr;
		/** CONSERVATIVE EXTENSION:
		 *   PROVE THAT THE FOLLOWING ASSINGMENT IS REDUNDANT
		 */
		entr_arr = ConservativeExtension.retrieveSortedMessages();
		//@set b = entr_arr;

		byte[] signedResult = postProcess(entr_arr);

		return signedResult;
	}




	/**
	 * TO BE PROVEN: The method returns the sorted input
	 * By proving that Utils.sort also return the sorted input, we obtain that
	 * the next assignment is redundant
	 */


	/*@
	  requires entr_arr != null;	  
	  ensures \dl_seqPerm(\dl_array2seq(\result), \dl_array2seq(entr_arr));
	  ensures (\forall int i; 0 <= i && i < entr_arr.length; Utils.compare(entr_arr[i],entr_arr[i+1]) <= 0);	  
	@*/	
	private byte[][] sort(byte[][] entr_arr) {
		if (entr_arr != null) {
			// sort the entries
			Utils.sort(entr_arr, 0, entr_arr.length);
			return entr_arr;
		} else {
			return new byte[][] {};
		}
	}
	/*
	 * We assume this method returns a permutation of the array 'msg'.
	 */
	/*@
	  ensures \result != null;
	  ensures \dl_seqPerm( \dl_array2seq(\result), \dl_array2seq(msg)); 
	  assignable \strictly_nothing; 
	 @*/
	private byte[][] extractBallots(byte[] ballotsAsAMessage) throws ServerMisbehavior{
		//ArrayList<byte[]> entries = new ArrayList<byte[]>();
		EntryList entries = new EntryList();

		// Loop over the input entries 
		byte[] last = null;
		//int numberOfEntries = 0;
		for( MessageSplitIter iter = new MessageSplitIter(ballotsAsAMessage); iter.notEmpty(); iter.next() ) {
			byte[] current = iter.current();
			if (last!=null && Utils.compare(last, current)>0)
				throw new ServerMisbehavior(-2, "Ballots not sorted");
			if (last!=null && Utils.compare(last, current)==0)
				throw new ServerMisbehavior(-3, "Duplicate ballots"); 
			last = current;
			byte[] decryptedBallot = decryptor.decrypt(current); // decrypt the current ballot
			if (decryptedBallot == null){
				//System.out.println("[MixServer.java] Decryption failed for ballot #" + numberOfEntries);
				continue;
			}
			byte[] elID = MessageTools.first(decryptedBallot);
			if (elID!=null || MessageTools.equal(elID, electionID)) // otherwise ballot is invalid and we ignore it
				entries.add(MessageTools.second(decryptedBallot));
			else {
				try {
					//System.out.println("[MixServer.java] Ballot #" + numberOfEntries + " invalid");
				} catch (Throwable t) {}
			}
			//++numberOfEntries;
		}

		byte[][] entr_arr = new byte[entries.size()][];
		entries.toArray(entr_arr);
		return entr_arr;
	}
	/*
	 * Since this method is called after the redundant statement, we don't care what it does.
	 * We assume it doesn't change any fields.
	 */
	/*@
	  ensures true;
	  assignable \strictly_nothing;
	 @*/
	private byte[] postProcess(byte[][] entr_arr) {
		// format entries as one message
		byte[] entriesAsAMessage = Utils.concatenateMessageArray(entr_arr, entr_arr.length);


		// add election id, tag and sign
		byte[] elID_entriesAsAMessage = MessageTools.concatenate(electionID, entriesAsAMessage);
		byte[] result = MessageTools.concatenate(Tag.BALLOTS, elID_entriesAsAMessage);
		byte[] signatureOnResult = signer.sign(result);
		byte[] signedResult = MessageTools.concatenate(result, signatureOnResult);
		return signedResult;
	}
	
	/*
	 * We assume it doesn't change any fields.
	 */
	/*@
	  public normal_behaviour
	  ensures true;
	  assignable \strictly_nothing;
	 @*/
	private byte[] checkAndGetBallots(byte[] data) throws MalformedData {
		// verify the signature of previous server
		byte[] tagged_payload = MessageTools.first(data);
		byte[] signature = MessageTools.second(data);
		if (!precServVerif.verify(signature, tagged_payload))
			throw new MalformedData(1, "Wrong signature");

		// check the tag
		byte[] tag = MessageTools.first(tagged_payload);
		if (!MessageTools.equal(tag, Tag.BALLOTS))
			throw new MalformedData(2, "Wrong tag");		
		byte[] payload = MessageTools.second(tagged_payload);

		// check the election id 
		byte[] el_id = MessageTools.first(payload);
		if (!MessageTools.equal(el_id, electionID))
			throw new MalformedData(3, "Wrong election ID");

		// retrieve and process ballots (store decrypted entries in 'entries')
		byte[] ballotsAsAMessage = MessageTools.second(payload);
		return ballotsAsAMessage;
	}


	// methods for testing
	public Encryptor getEncryptor(){
		return decryptor.getEncryptor();
	}	
	public Verifier getVerifier(){
		return signer.getVerifier();
	}
}
