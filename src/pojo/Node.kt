package pojo

/**
 * Created by Ethan on 16/6/3.
 */
data class Node(var proposition: Proposition, var level: Int, var parentNode: Node?, var leftChild: Node?, var rightChild: Node?) {
    override fun toString(): String {
        return "a{proposition=$proposition, level=$level, parentNode=${parentNode?.proposition}, " +
                "leftChild=${leftChild?.proposition}, rightChild=${rightChild?.proposition}"
    }
}