import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

public class TxHandler {
    private UTXOPool pool;

    /**
     * Creates a public ledger whose current UTXOPool (collection of unspent transaction outputs) is
     * {@code utxoPool}. This should make a copy of utxoPool by using the UTXOPool(UTXOPool uPool)
     * constructor.
     */
    public TxHandler(UTXOPool utxoPool) {
        this.pool = new UTXOPool(utxoPool);
    }

    /**
     * @return true if:
     * (1) all outputs claimed by {@code tx} are in the current UTXO pool, 
     * (2) the signatures on each input of {@code tx} are valid, 
     * (3) no UTXO is claimed multiple times by {@code tx},
     * (4) all of {@code tx}s output values are non-negative, and
     * (5) the sum of {@code tx}s input values is greater than or equal to the sum of its output
     *     values; and false otherwise.
     */
    public boolean isValidTx(Transaction tx) {
        // (1) all outputs claimed by {@code tx} are in the current UTXO pool,
        // (2) the signatures on each input of {@code tx} are valid,
        for (int i = 0; i < tx.numInputs(); ++i) {
            if (!this.isInputValid(tx, i))
                return false;
        }

        //  (3) no UTXO is claimed multiple times by {@code tx},
        Set<UTXO> ins = new HashSet<UTXO>();
        for (Transaction.Input in : tx.getInputs()) {
            ins.add(inputToUTXO(in));
        }
        if (tx.numInputs() != ins.size()) {
            return false;
        }

        // (4) all of {@code tx}s output values are non-negative, and
        for (Transaction.Output out : tx.getOutputs()) {
            if (out.value < 0)
                return false;
        }

        // (5) the sum of {@code tx}s input values is greater than or equal to the sum of its output
        //     values; and false otherwise.
        double inSum = 0.0;
        double outSum = 0.0;
        for (Transaction.Output out : tx.getOutputs())
            outSum += out.value;
        for (Transaction.Input in : tx.getInputs())
            inSum += getOutputByInput(in).value;

        if (inSum < outSum)
            return false;

        return true;
    }

    /**
     * Handles each epoch by receiving an unordered array of proposed transactions, checking each
     * transaction for correctness, returning a mutually valid array of accepted transactions, and
     * updating the current UTXO pool as appropriate.
     */
    public Transaction[] handleTxs(Transaction[] possibleTxs) {
        ArrayList<Transaction> dedupedTxs = removeDoubleSpending(possibleTxs);
        ArrayList<Transaction> acceptedTxs = new ArrayList<Transaction>();

        for (Transaction tx : dedupedTxs) {
            addTransaction(tx);
            acceptedTxs.add(tx);
        }

        Transaction[] out = new Transaction[acceptedTxs.size()];
        out = acceptedTxs.toArray(out);
        return out;
    }

    private void addTransaction(Transaction tx) {
        for (int i = 0; i < tx.numOutputs(); ++i) {
            Transaction.Output out = tx.getOutput(i);
            UTXO utxo = new UTXO(tx.getHash(), i);

            pool.addUTXO(utxo, out);
        }

        for (Transaction.Input in : tx.getInputs()) {
            pool.removeUTXO(inputToUTXO(in));
        }
    }

    private boolean isInputValid(Transaction tx, int index) {
        byte[] message = tx.getRawDataToSign(index);
        Transaction.Input in = tx.getInput(index);
        Transaction.Output out = getOutputByInput(in);
        if (out == null)
            return false;

        return Crypto.verifySignature(out.address, message, in.signature);
    }

    private UTXO inputToUTXO(Transaction.Input in) {
        return new UTXO(in.prevTxHash, in.outputIndex);
    }

    private Transaction.Output getOutputByInput(Transaction.Input in) {
        return pool.getTxOutput(inputToUTXO(in));
    }

    private ArrayList<Transaction> removeDoubleSpending(Transaction[] txs) {
        TxHandler handler = new TxHandler(pool);
        ArrayList<Transaction> out = new ArrayList<Transaction>();

        for (Transaction tx : txs) {
            if (!handler.isValidTx(tx)) continue;

            handler.addTransaction(tx);
            out.add(tx);
        }

        return out;
    }

    public UTXOPool getUTXOPool() {
        return this.pool;
    }
}
