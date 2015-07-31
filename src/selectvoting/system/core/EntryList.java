package selectvoting.system.core;


public class EntryList {

		static class Node 
		{
			public byte[] entry;
			public Node next;

			public Node(byte[] entry) 
			{
				this.entry = entry;
				this.next=null;
			}
		}

		private Node head, last;
		private int size;

		
		public EntryList(){
			head=last=null;
			size=0;
		}
		
		public void add(byte[] entry) 
		{
			Node newEntry=new Node(entry);
			if(head==null)
				head=last=newEntry;
			else {
				Node tmp = last;
				if (last == tmp && tmp != null) {
					tmp.next = newEntry;
				}
				last = tmp;
			}
			size++;
		}
		
		public int size(){
			return size;
		}
		
		public void toArray(byte[][] arr)
		{
			int i=0;
			Node tmp = head;
			while (tmp != null) {
				byte[] x = tmp.entry;
				try {
					arr[i] = x;
				} catch (Throwable t) {}
				i++;
				tmp = tmp.next;
			}
		}		
}