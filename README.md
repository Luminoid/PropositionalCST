# PropositionalCST
An algorithm for CST with premises in propositional logic

## 功能
使用 Complete systematic tableaux with premises 对某个 proposition 进行表证明。如果证明失败，会给出反例。

## 使用方式
PropositionalCST_jar 文件夹内包含可直接运行的 jar 文件。
程序会识别 input 文件夹中的 test.txt 文件，只要把想测试的文件名称改成 test.txt 即可进行测试。
input 文件夹内一共包含4个测试样例，第三个样例含counterexample。
输出内容在output/result.txt中。

## 注意事项
- 本程序使用 kotlin 语言在 IntelliJ 平台上开发，项目可以直接用 IntelliJ 打开
- 测试文件中，操作符两边至少各要有一个空格（如果没有会抛出格式错误的异常）
