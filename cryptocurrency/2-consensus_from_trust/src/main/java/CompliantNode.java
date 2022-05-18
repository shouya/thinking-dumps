import java.util.HashSet;
import java.util.Set;

/* CompliantNode refers to a node that follows the rules (not malicious)*/
public class CompliantNode implements Node {
    private Set<Transaction> pendingTxs;

    public CompliantNode(double p_graph, double p_malicious, double p_txDistribution, int numRounds) {
        this.pendingTxs = new HashSet<Transaction>();
    }

    public void setFollowees(boolean[] followees) {
    }

    public void setPendingTransaction(Set<Transaction> pendingTransactions) {
        for (Transaction tx : pendingTransactions) {
            this.pendingTxs.add(tx);
        }
    }

    public Set<Transaction> sendToFollowers() {
        Set<Transaction> toSend = new HashSet<Transaction>();
        for (Transaction tx : pendingTxs) {
            toSend.add(tx);
        }
        pendingTxs.clear();
        return toSend;
    }

    public void receiveFromFollowees(Set<Candidate> candidates) {
        for (Candidate c : candidates) {
            pendingTxs.add(c.tx);
        }
    }
}
