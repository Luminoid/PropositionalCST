import pojo.*
import java.io.File
import java.io.IOException
import java.util.*
import kotlin.text.Regex

/**
 * Created by Ethan on 16/6/4.
 */

class Parse() {
    public fun parseFile(fileName: String) {
        var filePath = "./input/" + fileName
        try {
            var file = File(filePath)
            var fileContent = file.readLines()
            constructTree(fileContent)
        } catch(e: IOException) {
            e.printStackTrace()
        }
    }

    private fun constructTree(propList: List<String>) {
        var tree: Tree
        var unreducedNodeList: MutableList<Node> = ArrayList()

        // root
        var root = Node(parseProposition(propList[0]), 0, null, null, null)
        root.proposition.sign = false
        tree = Tree(root)
        unreducedNodeList.add(root)
        reduceNode(unreducedNodeList)

        // premises
        propList.drop(2).forEach {
            addNode(it, unreducedNodeList, root)
            reduceNode(unreducedNodeList)
        }
        while (unreducedNodeList.size != 0) {
            reduceNode(unreducedNodeList)
        }
        //        printTreeStructure(root)
        printReduceSequence(root)
        printCounterExample(findCounterExample(root), root)
    }

    private fun addNode(rawProposition: String, unreducedNodeList: MutableList<Node>, root: Node) {
        getUnfinishedLeafList(root).forEach {
            var node = Node(parseProposition(rawProposition), 0, null, null, null)
            it.leftChild = node
            node.parentNode = it
            node.level = it.level + 1
            unreducedNodeList.add(node)
        }
    }

    private fun reduceNode(unreducedNodeList: MutableList<Node>) {
        var tmpList: MutableList<Node> = ArrayList()
        tmpList.addAll(unreducedNodeList)
        unreducedNodeList.clear()
        tmpList.sortedBy { it.level }.forEach { node ->
            when {
                node.proposition.topLevelSymbolIndex == 0
                -> {
                    if (isContradictory(node)) {
                        getLeafNodeList(node).forEach {
                            var contradictoryNode = Node(Proposition(false, ArrayList<Symbol>(), 0, ""),
                                    it.level + 1, it, null, null)
                            it.leftChild = contradictoryNode
                        }
                    }
                }

                node.proposition.topLevelSymbolIndex == 1
                -> {
                    var symbolList = node.proposition.content
                    var childSymbolList = symbolList.subList(2, symbolList.size - 1)
                    var topLevelSymbolIndex = getTopLevelSymbolIndex(childSymbolList)
                    var topLevelSymbol = childSymbolList[topLevelSymbolIndex].value
                    var sign = !node.proposition.sign
                    getLeafNodeList(node).forEach {
                        var reducedNode = node.copy(level = it.level + 1, parentNode = it, leftChild = null, rightChild = null)
                        it.leftChild = reducedNode
                        var onlyChildNode = Node(Proposition(sign, childSymbolList, topLevelSymbolIndex, topLevelSymbol),
                                reducedNode.level + 1, reducedNode, null, null)
                        reducedNode.leftChild = onlyChildNode
                        unreducedNodeList.add(onlyChildNode)
                    }
                }

                node.proposition.topLevelSymbol == "\\eq"
                -> {
                    var symbolList = node.proposition.content
                    var leftChild1SymbolList = symbolList.subList(1, node.proposition.topLevelSymbolIndex)
                    var leftChild2SymbolList = symbolList.subList(node.proposition.topLevelSymbolIndex + 1, symbolList.size - 1)
                    var rightChild1SymbolList = symbolList.subList(1, node.proposition.topLevelSymbolIndex)
                    var rightChild2SymbolList = symbolList.subList(node.proposition.topLevelSymbolIndex + 1, symbolList.size - 1)
                    var topLevelSymbolIndex1 = getTopLevelSymbolIndex(leftChild1SymbolList)
                    var topLevelSymbolIndex2 = getTopLevelSymbolIndex(leftChild2SymbolList)
                    var topLevelSymbolIndex3 = getTopLevelSymbolIndex(rightChild1SymbolList)
                    var topLevelSymbolIndex4 = getTopLevelSymbolIndex(rightChild2SymbolList)
                    var topLevelSymbol1 = leftChild1SymbolList[topLevelSymbolIndex1].value
                    var topLevelSymbol2 = leftChild2SymbolList[topLevelSymbolIndex2].value
                    var topLevelSymbol3 = rightChild1SymbolList[topLevelSymbolIndex3].value
                    var topLevelSymbol4 = rightChild2SymbolList[topLevelSymbolIndex4].value
                    var sign1: Boolean
                    var sign2: Boolean
                    var sign3: Boolean
                    var sign4: Boolean
                    if (node.proposition.sign == true) {
                        sign1 = true
                        sign2 = true
                        sign3 = false
                        sign4 = false
                    } else {
                        sign1 = true
                        sign2 = false
                        sign3 = false
                        sign4 = true
                    }
                    getLeafNodeList(node).forEach {
                        var reducedNode = node.copy(level = it.level + 1, parentNode = it, leftChild = null, rightChild = null)
                        it.leftChild = reducedNode
                        var leftChild1Node = Node(Proposition(sign1, leftChild1SymbolList, topLevelSymbolIndex1,
                                topLevelSymbol1), reducedNode.level + 1, reducedNode, null, null)
                        var leftChild2Node = Node(Proposition(sign2, leftChild2SymbolList, topLevelSymbolIndex2,
                                topLevelSymbol2), reducedNode.level + 2, leftChild1Node, null, null)
                        var rightChild1Node = Node(Proposition(sign3, rightChild1SymbolList, topLevelSymbolIndex3,
                                topLevelSymbol3), reducedNode.level + 1, reducedNode, null, null)
                        var rightChild2Node = Node(Proposition(sign4, leftChild2SymbolList, topLevelSymbolIndex4,
                                topLevelSymbol4), reducedNode.level + 2, rightChild1Node, null, null)
                        reducedNode.leftChild = leftChild1Node
                        reducedNode.rightChild = rightChild1Node
                        leftChild1Node.leftChild = leftChild2Node
                        rightChild1Node.leftChild = rightChild2Node
                        unreducedNodeList.add(leftChild1Node)
                        unreducedNodeList.add(leftChild2Node)
                        unreducedNodeList.add(rightChild1Node)
                        unreducedNodeList.add(rightChild2Node)
                    }
                }

                (node.proposition.topLevelSymbol == "\\and" && node.proposition.sign == false) ||
                        (node.proposition.topLevelSymbol == "\\or" && node.proposition.sign == true) ||
                        (node.proposition.topLevelSymbol == "\\imply" && node.proposition.sign == true)
                -> {
                    var symbolList = node.proposition.content
                    var leftChildSymbolList = symbolList.subList(1, node.proposition.topLevelSymbolIndex)
                    var rightChildSymbolList = symbolList.subList(node.proposition.topLevelSymbolIndex + 1, symbolList.size - 1)
                    var topLevelSymbolIndex1 = getTopLevelSymbolIndex(leftChildSymbolList)
                    var topLevelSymbolIndex2 = getTopLevelSymbolIndex(rightChildSymbolList)
                    var topLevelSymbol1 = leftChildSymbolList[topLevelSymbolIndex1].value
                    var topLevelSymbol2 = rightChildSymbolList[topLevelSymbolIndex2].value
                    var sign1: Boolean
                    var sign2: Boolean
                    if (node.proposition.topLevelSymbol == "\\and") {
                        sign1 = false
                        sign2 = false
                    } else if (node.proposition.topLevelSymbol == "\\or") {
                        sign1 = true
                        sign2 = true
                    } else {
                        sign1 = false
                        sign2 = true
                    }
                    getLeafNodeList(node).forEach {
                        var reducedNode = node.copy(level = it.level + 1, parentNode = it, leftChild = null, rightChild = null)
                        it.leftChild = reducedNode
                        var leftChildNode = Node(Proposition(sign1, leftChildSymbolList, topLevelSymbolIndex1,
                                topLevelSymbol1), reducedNode.level + 1, reducedNode, null, null)
                        var rightChildNode = Node(Proposition(sign2, rightChildSymbolList, topLevelSymbolIndex2,
                                topLevelSymbol2), reducedNode.level + 1, reducedNode, null, null)
                        reducedNode.leftChild = leftChildNode
                        reducedNode.rightChild = rightChildNode
                        unreducedNodeList.add(leftChildNode)
                        unreducedNodeList.add(rightChildNode)
                    }
                }

                (node.proposition.topLevelSymbol == "\\and" && node.proposition.sign == true) ||
                        (node.proposition.topLevelSymbol == "\\or" && node.proposition.sign == false) ||
                        (node.proposition.topLevelSymbol == "\\imply" && node.proposition.sign == false)
                -> {
                    var symbolList = node.proposition.content
                    var leftChild1SymbolList = symbolList.subList(1, node.proposition.topLevelSymbolIndex)
                    var leftChild2SymbolList = symbolList.subList(node.proposition.topLevelSymbolIndex + 1, symbolList.size - 1)
                    var topLevelSymbolIndex1 = getTopLevelSymbolIndex(leftChild1SymbolList)
                    var topLevelSymbolIndex2 = getTopLevelSymbolIndex(leftChild2SymbolList)
                    var topLevelSymbol1 = leftChild1SymbolList[topLevelSymbolIndex1].value
                    var topLevelSymbol2 = leftChild2SymbolList[topLevelSymbolIndex2].value
                    var sign1: Boolean
                    var sign2: Boolean
                    if (node.proposition.topLevelSymbol == "\\and") {
                        sign1 = true
                        sign2 = true
                    } else if (node.proposition.topLevelSymbol == "\\or") {
                        sign1 = false
                        sign2 = false
                    } else {
                        sign1 = true
                        sign2 = false
                    }
                    getLeafNodeList(node).forEach {
                        var reducedNode = node.copy(level = it.level + 1, parentNode = it, leftChild = null, rightChild = null)
                        it.leftChild = reducedNode
                        var leftChild1Node = Node(Proposition(sign1, leftChild1SymbolList, topLevelSymbolIndex1,
                                topLevelSymbol1), reducedNode.level + 1, reducedNode, null, null)
                        var leftChild2Node = Node(Proposition(sign2, leftChild2SymbolList, topLevelSymbolIndex2,
                                topLevelSymbol2), reducedNode.level + 2, leftChild1Node, null, null)
                        reducedNode.leftChild = leftChild1Node
                        leftChild1Node.leftChild = leftChild2Node
                        unreducedNodeList.add(leftChild1Node)
                        unreducedNodeList.add(leftChild2Node)
                    }
                }
            }
        }
    }

    private fun parseProposition(rawProposition: String): Proposition {
        var symbolList: MutableList<Symbol> = ArrayList()
        var token = ""
        for (i in rawProposition.indices) {
            token += rawProposition[i]
            var symbol = if (i != rawProposition.length - 1)
                isSymbolValid(token, rawProposition[i + 1] + "") else isSymbolValid(token, "")
            symbol?.let {
                symbol.value = symbol.value.trim()
                symbolList.add(symbol)
                token = ""
            }
        }
        if (token.length != 0) throw Exception("Input file's format is incorrect!")
        var topLevelSymbolIndex = getTopLevelSymbolIndex(symbolList)
        return Proposition(true, symbolList, topLevelSymbolIndex, symbolList[topLevelSymbolIndex].value)
    }

    private fun printTreeStructure(node: Node) {
        for (i in 1..node.level) print("\t")
        node.proposition.content.forEach { print(it.value) }
        println()
        if (node.leftChild != null) {
            printTreeStructure(node.leftChild!!)
        }
        if (node.rightChild != null) {
            printTreeStructure(node.rightChild!!)
        }
    }

    private fun printReduceSequence(root: Node) {
        var nodes: MutableList<MutableList<Node>> = ArrayList()
        fun enumerateNode(node: Node) {
            if (node.proposition.content.size != 0) {
                while (node.level >= nodes.size) {
                    nodes.add(ArrayList())
                }
                nodes[node.level].add(nodes[node.level].size, node)
                node.leftChild?.let {
                    enumerateNode(node.leftChild!!)
                }
                node.rightChild?.let {
                    enumerateNode(node.rightChild!!)
                }
            }
        }
        enumerateNode(root)
        nodes.forEach {
            it.forEach { node ->
                if (node.proposition.sign) print("T ") else print("F ")
                node.proposition.content.forEach { symbol ->
                    if (symbol.symbolType != SymbolType.UNARY_CONNECTIVE && symbol.symbolType != SymbolType.BINARY_CONNECTIVE)
                        print(symbol.value) else print(" ${symbol.value} ")
                }
                println("")
            }
        }
    }

    private fun isSymbolValid(s: String, c: String) = when {
        s.matches(Regex("\\s+\\\\and\\s")) -> Symbol(s, SymbolType.BINARY_CONNECTIVE)
        s.matches(Regex("\\s+\\\\or\\s")) -> Symbol(s, SymbolType.BINARY_CONNECTIVE)
        s.matches(Regex("\\s+\\\\imply\\s")) -> Symbol(s, SymbolType.BINARY_CONNECTIVE)
        s.matches(Regex("\\s+\\\\eq\\s")) -> Symbol(s, SymbolType.BINARY_CONNECTIVE)
        s.matches(Regex("\\s+\\\\not\\s")) -> Symbol(s, SymbolType.UNARY_CONNECTIVE)
        s.matches(Regex("\\s*\\(")) -> Symbol(s, SymbolType.LEFT_PARENTHESIS)
        s.matches(Regex("\\s*\\)")) -> Symbol(s, SymbolType.RIGHT_PARENTHESIS)
        s.matches(Regex("\\s*[A-Z]+(_\\{([0-9])*\\})?")) && !c.matches(Regex("[A-Z_]")) -> Symbol(s, SymbolType.PROPOSITIONAL_LETTER)
        else -> null
    }

    private fun getTopLevelSymbolIndex(symbolList: List<Symbol>): Int {
        if (symbolList[0].symbolType == SymbolType.PROPOSITIONAL_LETTER) return 0             // Propositional Letter
        if (symbolList[1].symbolType == SymbolType.UNARY_CONNECTIVE) return 1                 // Unary Connective
        var balance = 0
        var index = 0
        symbolList.forEach {
            when {
                it.symbolType == SymbolType.LEFT_PARENTHESIS -> balance++
                it.symbolType == SymbolType.RIGHT_PARENTHESIS -> balance--
                it.symbolType == SymbolType.BINARY_CONNECTIVE && balance == 1 -> return index // Binary Connective
            }
            index++
        }
        throw Exception("Input file's format is incorrect!")
    }

    private fun isContradictory(node: Node): Boolean {
        var nodePointer = node.parentNode
        while (nodePointer != null) {
            if (nodePointer.proposition.content == node.proposition.content
                    && nodePointer.proposition.sign != node.proposition.sign) return true
            nodePointer = nodePointer.parentNode
        }
        return false
    }

    private fun getLeafNodeList(node: Node): List<Node> {
        var leafNodeList: MutableList<Node> = ArrayList()
        fun getLeafNode(node: Node) {
            if (node.leftChild == null && node.rightChild == null && node.proposition.content.size != 0) {
                // Leaf Node
                leafNodeList.add(node)
            } else {
                if (node.leftChild != null) {
                    getLeafNode(node.leftChild!!)
                }
                if (node.rightChild != null) {
                    getLeafNode(node.rightChild!!)
                }
            }
        }
        getLeafNode(node)
        return leafNodeList
    }

    private fun getUnfinishedLeafList(root: Node) = getLeafNodeList(root)

    private fun findCounterExample(root: Node): Node? {
        var leafNodeList = getLeafNodeList(root)
        if (leafNodeList.size == 0) return null else return leafNodeList[0]
    }

    private fun printCounterExample(node: Node?, root: Node) {
        println()
        if (node == null)
            println("There doesn't exist counter example")
        else {
            var trueAssignment: MutableList<String> = ArrayList()
            node.let {
                var nodePointer = node
                while (nodePointer != null) {
                    if (node.proposition.topLevelSymbolIndex == 0 && node.proposition.sign == true) {
                        trueAssignment.add(node.proposition.topLevelSymbol)
                    }
                    nodePointer = nodePointer.parentNode
                }
            }
            println("Counter Example: ")
            root.proposition.content.filter { it.symbolType == SymbolType.PROPOSITIONAL_LETTER }.map { it.value }.forEach {
                if (trueAssignment.contains(it)) print("$it: True ") else print("$it: False ")
            }
        }
    }
}