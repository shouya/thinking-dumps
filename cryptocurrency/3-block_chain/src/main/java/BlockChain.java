// Block Chain should maintain only limited block nodes to satisfy the functions
// You should not have all the blocks added to the block chain in memory 
// as it would cause a memory overflow.

import java.util.ArrayList;

public class BlockChain {
    public static final int CUT_OFF_AGE = 10;

    public class ChainNode {
        ChainNode prev;
        int height;
        Block block;
        UTXOPool pool;
        boolean is_head;

        public ChainNode(ChainNode prev, Block blk) {
            this.prev = prev;
            if (prev != null)
                this.height = prev.height + 1;
            else
                this.height = 1;
            this.block = blk;

            TxHandler handler = new TxHandler(
                    prev != null ? prev.pool : new UTXOPool()
            );
            ArrayList<Transaction> txs = blk.getTransactions();
            handler.handleTxs(txs.toArray(new Transaction[0]));
            this.pool = handler.getUTXOPool();
            Transaction coinbase = blk.getCoinbase();
            if (coinbase == null)
                return;
            this.pool.addUTXO(
                    new UTXO(coinbase.getHash(), 0),
                    coinbase.getOutput(0)
            );
        }

        public void registerHead(ArrayList<ChainNode> heads) {
            if (this.prev != null && this.prev.is_head) {
                this.prev.is_head = false;
                heads.remove(this.prev);
            }
            this.is_head = true;
            heads.add(this);
        }
    }

    TransactionPool txpool;
    ArrayList<ChainNode> heads;

    /**
     * create an empty block chain with just a genesis block. Assume {@code genesisBlock} is a valid
     * block
     */
    public BlockChain(Block genesisBlock) {
        heads = new ArrayList<ChainNode>();
        txpool = new TransactionPool();

        ChainNode genesis = new ChainNode(null, genesisBlock);
        genesis.registerHead(heads);
    }

    /** Get the maximum height block */
    public Block getMaxHeightBlock() {
        return getTallestHead().block;
    }

    /** Get the UTXOPool for mining a new block on top of max height block */
    public UTXOPool getMaxHeightUTXOPool() {
        return getTallestHead().pool;
    }

    /** Get the transaction pool to mine a new block */
    public TransactionPool getTransactionPool() {
        return txpool;
    }

    /**
     * Add {@code block} to the block chain if it is valid. For validity, all transactions should be
     * valid and block should be at {@code height > (maxHeight - CUT_OFF_AGE)}.
     * 
     * <p>
     * For example, you can try creating a new block over the genesis block (block height 2) if the
     * block chain height is {@code <=
     * CUT_OFF_AGE + 1}. As soon as {@code height > CUT_OFF_AGE + 1}, you cannot create a new block
     * at height 2.
     * 
     * @return true if block is successfully added
     */
    public boolean addBlock(Block block) {
        ChainNode parent = getParent(block);
        if (parent == null)
            return false;

        ArrayList<Transaction> txs = block.getTransactions();

        TxHandler handler = new TxHandler(parent.pool);
        Transaction[] txs_ = handler.handleTxs(txs.toArray(new Transaction[0]));

        // validates transactions in the block
        if (txs_.length != txs.size())
            return false;


        ChainNode node = new ChainNode(parent, block);

        // validates block have enough height
        if (node.height <= getTallestHead().height - CUT_OFF_AGE)
            return false;

        node.registerHead(heads);
        return true;
    }

    private TransactionPool extractTransactionPool(Block block) {
        TransactionPool txpool = new TransactionPool();
        for (Transaction tx : block.getTransactions()) {
            txpool.addTransaction(tx);
        }
        return txpool;
    }

    private ChainNode getParent(Block block) {
        if (block.getPrevBlockHash() == null)
            return null;

        ByteArrayWrapper hash = new ByteArrayWrapper(block.getPrevBlockHash());
        for (ChainNode node : heads) {
            ChainNode parent = getParentHelper(node, hash);
            if (parent != null)
                return parent;
        }
        return null;
    }

    private ChainNode getParentHelper(ChainNode node, ByteArrayWrapper hash) {
        if (new ByteArrayWrapper(node.block.getHash()).equals(hash)) {
            return node;
        }
        if (node.prev == null)
            return null;
        return getParentHelper(node.prev, hash);
    }

    private ChainNode getTallestHead() {
        ChainNode tallest = null;
        for (ChainNode h : heads) {
            if (tallest == null || tallest.height < h.height)
                tallest = h;
        }
        return tallest;
    }

    /** Add a transaction to the transaction pool */
    public void addTransaction(Transaction tx) {
        txpool.addTransaction(tx);
    }
}