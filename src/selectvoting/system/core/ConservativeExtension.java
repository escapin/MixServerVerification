package selectvoting.system.core;

import de.unitrier.infsec.utils.MessageTools;

public class ConservativeExtension
{
	private static byte[][] messages;
	
	public static void storeMessages(byte[][] msg)
	{
		messages=MessageTools.copyOf(msg);
	}
	
	public static byte[][] retrieveSortedMessages()
	{
		Utils.sort(messages, 0, messages.length);
		return messages;
	}
}
