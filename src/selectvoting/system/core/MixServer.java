package selectvoting.system.core;

import de.unitrier.infsec.functionalities.digsig.Signer;
import de.unitrier.infsec.functionalities.digsig.Verifier;
import de.unitrier.infsec.functionalities.pkenc.Decryptor;
import de.unitrier.infsec.functionalities.pkenc.Encryptor;
import de.unitrier.infsec.utils.MessageTools;
import selectvoting.system.core.Utils.MessageSplitIter;

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
	@SuppressWarnings("serial")
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
	@SuppressWarnings("serial")
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
	public byte[] processBallots(byte[] data) throws MalformedData, ServerMisbehavior {
		byte[] ballotsAsAMessage = checkAndGetBallots(data);
		
		byte[][] entr_arr = extractBallots(ballotsAsAMessage);
		
		checkBallotsSorted(entr_arr);
		
		// sort the entries
		Utils.sort(entr_arr, 0, entr_arr.length);
		
		/** CONSERVATIVE EXTENSION:
		 * 	 PROVE THAT THE FOLLOWING ASSINGMENT IS REDUNDANT
		 */
		entr_arr = ConservativeExtension.retrieveSortedMessages(); 
				
		byte[] signedResult = postProcess(entr_arr);
		
		return signedResult;
	}

	private byte[][] extractBallots(byte[] ballotsAsAMessage) {
		//ArrayList<byte[]> entries = new ArrayList<byte[]>();
		EntryList entries = new EntryList();

		// Loop over the input entries 
		int numberOfEntries = 0;
		for( MessageSplitIter iter = new MessageSplitIter(ballotsAsAMessage); iter.notEmpty(); iter.next() ) {
			byte[] decryptedBallot = decryptor.decrypt(iter.current()); // decrypt the current ballot
			if (decryptedBallot == null){
				System.out.println("[MixServer.java] Decryption failed for ballot #" + numberOfEntries);
				continue;
			}
			byte[] elID = MessageTools.first(decryptedBallot);
			if (elID!=null || MessageTools.equal(elID, electionID)) // otherwise ballot is invalid and we ignore it
				entries.add(MessageTools.second(decryptedBallot));
			else {
				try {
					System.out.println("[MixServer.java] Ballot #" + numberOfEntries + " invalid");
				} catch (Throwable t) {}
			}
			++numberOfEntries;
		}
		
		byte[][] entr_arr = new byte[entries.size()][];
		entries.toArray(entr_arr);
		return entr_arr;
	}

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

	private void checkBallotsSorted(byte[][] entr_arr) throws ServerMisbehavior {
		for (int i= 1; i < entr_arr.length; i++) {
			byte[] last = entr_arr[i-1];
			byte[] current = entr_arr[i];
			if (last!=null && Utils.compare(last, current)>0)
				throw new ServerMisbehavior(-2, "Ballots not sorted");
			if (last!=null && Utils.compare(last, current)==0)
				throw new ServerMisbehavior(-3, "Duplicate ballots"); 
		}
	}

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
