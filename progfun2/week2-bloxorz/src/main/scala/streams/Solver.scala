package streams

import common._

/**
 * This component implements the solver for the Bloxorz game
 */
trait Solver extends GameDef {

  /**
   * Returns `true` if the block `b` is at the final position
   */
  def done(b: Block): Boolean = b.b1 == goal && b.b2 == goal

  /**
   * This function takes two arguments: the current block `b` and
   * a list of moves `history` that was required to reach the
   * position of `b`.
   * 
   * The `head` element of the `history` list is the latest move
   * that was executed, i.e. the last move that was performed for
   * the block to end up at position `b`.
   * 
   * The function returns a stream of pairs: the first element of
   * the each pair is a neighboring block, and the second element
   * is the augmented history of moves required to reach this block.
   * 
   * It should only return valid neighbors, i.e. block positions
   * that are inside the terrain.
   */
  def neighborsWithHistory(b: Block, history: List[Move]): Stream[(Block, List[Move])] = {
    val nova_vals = b.legalNeighbors map { case (bn,m) => (bn,m::history) }
    nova_vals.toStream
  }

  /**
   * This function returns the list of neighbors without the block
   * positions that have already been explored. We will use it to
   * make sure that we don't explore circular paths.
   */
  def newNeighborsOnly(neighbors: Stream[(Block, List[Move])],
                       explored: Set[Block]): Stream[(Block, List[Move])] = {
    neighbors filter (n => !(explored contains n._1))
  }

  /**
   * The function `from` returns the stream of all possible paths
   * that can be followed, starting at the `head` of the `initial`
   * stream.
   * 
   * The blocks in the stream `initial` are sorted by ascending path
   * length: the block positions with the shortest paths (length of
   * move list) are at the head of the stream.
   * 
   * The parameter `explored` is a set of block positions that have
   * been visited before, on the path to any of the blocks in the
   * stream `initial`. When search reaches a block that has already
   * been explored before, that position should not be included a
   * second time to avoid cycles.
   * 
   * The resulting stream should be sorted by ascending path length,
   * i.e. the block positions that can be reached with the fewest
   * amount of moves should appear first in the stream.
   * 
   * Note: the solution should not look at or compare the lengths
   * of different paths - the implementation should naturally
   * construct the correctly sorted stream.
   */
  def from(initial: Stream[(Block, List[Move])],
           explored: Set[Block]): Stream[(Block, List[Move])] = {
    initial match {
      case Stream.Empty => Stream.empty
      case Stream.cons(hd,tl) => {
	val explored_new = explored + hd._1
	val neigh_new = neighborsWithHistory(hd._1, hd._2)
	val neigh_new_filtered = newNeighborsOnly(neigh_new, explored_new)
	hd #:: from(tl ++: neigh_new_filtered, explored_new)
      }
    }
  }

  /**
   * The stream of all paths that begin at the starting block.
   */
  lazy val pathsFromStart: Stream[(Block, List[Move])] =
    from(Stream.cons((startBlock, List()), Stream.empty), Set.empty)
	 

  /**
   * Returns a stream of all possible pairs of the goal block along
   * with the history how it was reached.
   */
  lazy val pathsToGoal: Stream[(Block, List[Move])] =
    pathsFromStart filter {case (b,m) => done(b) }

  /**
   * The (or one of the) shortest sequence(s) of moves to reach the
   * goal. If the goal cannot be reached, the empty list is returned.
   *
   * Note: the `head` element of the returned list should represent
   * the first move that the player should perform from the starting
   * position.
   */
  lazy val solution: List[Move] =
    pathsToGoal.head._2
}
