# agda-mathlib

Try everying to define mathematical objects and proof theorems in agda.

这里是一个 agda 学习与交流的仓库，欢迎各位贡献！

简单来说，如果你有想用 agda 定义的数学概念，或者证明数学定理，都可以往这里丢！

目前这个仓库处在一个非常初始的阶段，所以你想写啥都可以：）

仓库的结构很简单（目前还没有配 CI），src 目录下是 agda 的源文件，为了避免与官方库的路径冲突，我们统一将实现放在 `src/Ext` 目录下。

在提交你的贡献之前不妨先看看 agda 的 module system 以及 agda-stdlib 的组织结构。简单概括就是

- 文件名、目录名尽量使用完整的首字母开头的单词（驼峰式命名）
- 可以有同名的目录和文件名（例如 `Data/Rational.agda` 与 `Data/Rational` 目录）
- 如果单个文件里的东西有点太多了可以试试把定义和性质分开。例如 `Data.Nat.Base` 里提供了大部分基础定义，而 `Data.Nat.Properties` 里提供了大量的相关性质。而 `Data.Nat` 基本上只是导入了 `Data.Nat.Base` 里的东西
- 名字里的花花符号比较多（x

当然，同一种概念可能有不同的定义，这个时候可以参考 `Data.Nat_≤_` 与 `Data.Nat._≤′_`，以及与之相关的定理 `≤⇒≤′` 和 `≤′⇒≤`。相信可以提供一个很好的设计和命名思路。

另外强烈建议在源文件中以注释的方式提供一定的解释，来帮助别人理解你的代码～

为了鼓励大家多多贡献，免去讨论增删的麻烦，我建议大家一开始先将自己的代码贡献到 `src/Experimental/<username>` 目录下。`<username>` 是你自己建的目录（首字母大写）。然后再提出 Issue/Pull Request 请求把你的实现作为项目的标准实现方式（或者替换掉原来的实现方式）。这样可以最大化地保护大家的贡献成果。毕竟 Agda 社区还是太小众了。

感谢所有参与贡献的开发者！