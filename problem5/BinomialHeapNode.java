public class BinomialHeapNode {

	public int key; 

	public int degree; 

	public BinomialHeapNode parent;

	public BinomialHeapNode sibling;

	public BinomialHeapNode child;
	
	public BinomialHeapNode() {}

	public BinomialHeapNode reverse(BinomialHeapNode sibl) {
		BinomialHeapNode ret;
		if (sibling != null)
			ret = sibling.reverse(this);
		else
			ret = this;
		sibling = sibl;
		return ret;
	}



}
