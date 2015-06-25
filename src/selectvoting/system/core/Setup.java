package selectvoting.system.core;

import selectvoting.system.core.Utils.MessageSplitIter;
import de.unitrier.infsec.environment.Environment;
import de.unitrier.infsec.functionalities.nonce.NonceGen;
import de.unitrier.infsec.functionalities.pkenc.Encryptor;
import de.unitrier.infsec.functionalities.pkenc.Decryptor;
import de.unitrier.infsec.functionalities.digsig.Signer;
import de.unitrier.infsec.functionalities.digsig.Verifier;
import de.unitrier.infsec.utils.MessageTools;

public final class Setup {

	// PURE SUPPORT METHODS:

	private static boolean setEquality(byte[][] arr1, byte[][] arr2) {
		if(arr1.length!=arr2.length) return false;
		byte[][] a1=MessageTools.copyOf(arr1);
		byte[][] a2=MessageTools.copyOf(arr2);
		Utils.sort(a1, 0, a1.length);
		Utils.sort(a2, 0, a2.length);
		for(int i=0;i<a1.length;i++)
			if(!MessageTools.equal(a1[i],a2[i])) 
				return false;
		return true;
	}
	
	
	// MAIN METHOD:
	
	// one secret bit
	private static boolean secret; // the HIGH value
	
	// the correct result
	static byte[][] correctResult; /** CONSERVATIVE EXTENSION */
	
	public static void main (String[] a) throws Throwable {


		// let the adversary choose how many messages have to 
		// be sent to the mix server
		int numberOfMessages = Environment.untrustedInput();
		
		
		// let the environment determine the two array of messages
		byte[][] msg1 = new byte[numberOfMessages][];
		byte[][] msg2 = new byte[numberOfMessages][];
		for(int i=0; i<numberOfMessages; ++i){
			msg1[i] = Environment.untrustedInputMessage();
			msg2[i] = Environment.untrustedInputMessage();
		}
		
		// the two sets represented by the two arrays must be equal
		if(!setEquality(msg1, msg2))
			throw new Throwable();
		
		// store the correct result of the mix server
		ConservativeExtension.getMessages(msg1); 
		
		byte[] electionID = Environment.untrustedInputMessage();
		
		
		// create the cryptographic functionalities
		Decryptor mixDecr = new Decryptor();
		Encryptor mixEncr = mixDecr.getEncryptor();
		Signer mixSign = new Signer();
		
		Signer precServSign = new Signer();
		Verifier precServVerif = precServSign.getVerifier(); 
		
		NonceGen noncegen = new NonceGen(); // nonce generation functionality
		
		
		MixServer mixServ = 
				new  MixServer(mixDecr, mixSign, precServVerif, electionID);
		
		
		// encrypt each message
		byte[][] encrMsg = new byte[numberOfMessages][];
		for(int i=0; i<numberOfMessages; ++i){
			byte[] msg = secret? msg1[i] : msg2[i];
			encrMsg[i] = mixEncr.encrypt(msg);
		}
			
		
		// FORMAT THE DATA FOR THE MIX SERVER
		
		Utils.sort(encrMsg, 0, encrMsg.length);
		
		byte[] asAMessage=Utils.concatenateMessageArray(encrMsg, encrMsg.length);
		// add election id, tag and sign
		byte[] elID_ballots = MessageTools.concatenate(electionID, asAMessage);
		byte[] input = MessageTools.concatenate(Tag.BALLOTS, elID_ballots);
		byte[] signatureOnInput = precServSign.sign(input);
		byte[] signedInput = MessageTools.concatenate(input, signatureOnInput);
		
		
		
		// let the mix server process the ballots 
		byte[] data=mixServ.processBallots(signedInput);
		
		

		byte[] tagged_payload = MessageTools.first(data);
		//byte[] signature = MessageTools.second(data);
		
		//byte[] tag = MessageTools.first(tagged_payload);
		byte[] payload = MessageTools.second(tagged_payload);
		//byte[] el_id = MessageTools.first(payload);
					
		// FINALLY WE GET THE FINAL RESULT
			
		byte[] finalResultAsAMessage = MessageTools.second(payload);
		
		byte[][] finalResult = new byte[numberOfMessages][];
		int numberOfEntries = 0;
		for( MessageSplitIter iter = new MessageSplitIter(finalResultAsAMessage); iter.notEmpty(); iter.next() ) {
			if (numberOfEntries >= numberOfMessages) // too many entries
				throw new Throwable();
			byte[] current = iter.current();
			byte[] elID = MessageTools.first(current);
			finalResult[numberOfEntries] = MessageTools.second(current);
			
			numberOfEntries++;
		}
		
		/** CONSERVATIVE EXTENSION:
		 * 	 PROVE THAT THE FOLLOWING ASSINGMENT IS REDUNDANT
		 */
		finalResult = ConservativeExtension.retrieveMessages();
		
		// We publish the final result
		for(int i=0; i<finalResult.length; i++)
			Environment.untrustedOutputMessage(finalResult[i]);
		
	}
}