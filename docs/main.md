# FormattedGraph 项目说明

## 项目目标

FormattedGraph 是一个 Lean 4 通用图可视化框架。用户在 Lean 中定义和修改图，并在
InfoView 中查看结果。修改源码后，Lean Server 会像更新证明状态一样，自动重新 elaboration
受影响的代码并更新图的显示。

这里的“图”用于组织和展示通用信息，不是以证明图论定理为目标的数学图库。

## 项目架构

项目实现时间较短，因此直接使用 ProofWidgets 的 `GraphDisplay`，不实现独立
Widget。

```text
Lean 中的领域数据
        ↓
通用 Graph 数据结构
        ↓
渲染转换
        ↓
ProofWidgets.GraphDisplay
        ↓
InfoView
```

### 1. 通用图结构

图结构需要支持：

- 有向图、孤立节点、自环和平行边。
- 节点和边各自具有稳定且唯一的 ID。
- 添加、删除、更新和查询节点与边。
- 删除节点时一并处理相连的边。
- 检查重复 ID、缺失端点等无效状态，并给出明确错误。

ID 与节点或边的数据必须分离。项目使用字符串 ID，由用户显式指定，例如
`"goal"`、`"step1"` 和 `"goal-to-step1"`。删除对象后不改变其他 ID；可以另外提供自动生成
`"n0"`、`"n1"` 等 ID 的辅助函数，但不重新编号。

节点和边的数据使用泛型参数：

```lean
Graph NodeData EdgeData
```

使用者可以通过 `structure` 或 `inductive` 定义业务数据，也可以使用
`Array (String × Lean.Json)` 等字典形式保存可扩展信息。节点数据可以包含字符串、数组、
自定义结构，或元编程环境中的 `Lean.Name`、`Lean.Expr` 等值；边的数据采用相同方式定义。

### 2. 渲染与 InfoView 接口

通用 Graph 只保存图的语义数据，不直接保存 HTML、颜色等显示信息。项目提供转换接口，
由使用者决定如何将 `NodeData` 和 `EdgeData` 转换为：

- `GraphDisplay.Vertex`
- `GraphDisplay.Edge`
- `GraphDisplay.Props`

转换可以运行在 `MetaM` 中，以便格式化 `Lean.Expr` 等元编程数据。

该部分分为两个阶段。

#### 阶段一：最终状态展示

提供如下显示入口：

```lean
#show_graph graphExpression
```

编辑 `graphExpression` 或它依赖的定义后，Lean Server 会重新 elaboration 该命令并更新
InfoView。Lean 代码始终是图的真实来源，不依赖外部 JSON 文件。

#### 阶段二：分步状态展示

尝试增加图操作 DSL，依次执行添加、删除和修改操作，并把每一步的 Graph 状态绑定到对应
源码位置。用户移动光标时，InfoView 显示执行到该步骤后的图。该阶段继续使用现有
`GraphDisplay`，不修改 ProofWidgets。

ProofWidgets 当前对平行边和自环的显示支持有限。后端保留这些结构，并在文档中说明显示
限制，不为此实现自定义前端。

## 交付标准

1. 在 Lean 中定义带有自定义节点数据和边数据的图。
2. 使用公共 API 增加、修改、删除和查询节点与边。
3. 对重复 ID、无效端点等输入给出清楚的错误信息。
4. 将图转换为 ProofWidgets `GraphDisplay` 所需数据。
5. 使用 `#show_graph` 在 InfoView 中显示图，并随源码修改自动更新。
6. 提供基本示例、测试和使用文档。
7. 验证图操作 DSL 和分步 InfoView 展示的可行性，并尽可能完成实现。

## 分工

1. 第一人负责 `Graph.lean`：图数据结构、增删改查、错误处理和单元测试。
2. 第二人负责 `Display.lean` 和 `Command.lean`：渲染转换与 `#show_graph` 最终状态展示。
3. 第三人负责示例、集成测试，并在 `DSL.lean` 中验证和实现分步状态展示。

三人应先共同确定 Graph 的公共读取接口和渲染转换接口，避免并行开发时重复修改同一文件。
