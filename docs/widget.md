# 阶段一：最终状态展示实现方案

## 目标

阶段一只实现最终图的 InfoView 展示：

```lean
#show_graph graphExpression
```

用户把光标放在该命令上时，InfoView 使用 ProofWidgets 的 `GraphDisplay` 显示
`graphExpression` 的最终状态。修改图或其依赖后，Lean Server 重新 elaboration，该命令重新
计算并更新显示。

本阶段不实现图操作 DSL、不保存每一步中间状态、不修改 ProofWidgets，也不支持从 Widget
反向修改 Lean 源码。

## 数据流

```text
GraphWithData ep
       ↓
Display.graphToProps
       ↓
GraphDisplay.Props
       ↓
Command.#show_graph
       ↓
Widget.savePanelWidgetInfo
       ↓
InfoView
```

Lean 代码是图的唯一数据源，不读取或生成外部 JSON 文件。

## 文件职责

### `FormattedGraph/Graph.lean`

提供现有后端：

- `FiniteDirectedGraph.Graph ep`
- `WithData.GraphWithData ep`
- 节点集合 `G.V` 和边集合 `G.E`
- 端点函数 `ep : ε → ν × ν`
- 节点数据 `G.data_v` 和边数据 `G.data_e`
- 图的增删改操作

Widget 代码只读取这些公开字段，不修改图结构实现。

### `FormattedGraph/Display.lean`

负责所有可复用的渲染逻辑：

- 定义节点和边的显示接口。
- 将 `GraphWithData ep` 转换为 `GraphDisplay.Props`。
- 将泛型节点 ID 转换为 ProofWidgets 使用的字符串 ID。
- 生成节点标签、详情、边标签和样式。
- 检查渲染后的重复节点 ID、平行边等不受支持的输入。
- 提供用于 InfoView 的顶层 `Html`。

该文件不能依赖 `Command.lean`，转换函数必须公开，以便测试和后续其他命令复用。

### `FormattedGraph/Command.lean`

只负责命令层：

- 定义 `#show_graph` 语法。
- elaborate 并检查图表达式。
- 查找渲染实例并调用 `Display.lean`。
- 将结果注册为当前位置的 Panel Widget。
- 将错误报告到 `#show_graph` 对应的源码位置。

该文件不重复实现节点和边的转换逻辑。

### `FormattedGraph.lean`

完成后统一导出：

```lean
import FormattedGraph.Graph
import FormattedGraph.Display
import FormattedGraph.Command
```

下游和示例最终只需：

```lean
import FormattedGraph
```

## Display 公共接口

### 显示描述

后端数据不直接保存 HTML 和颜色。`Display.lean` 定义两个轻量显示描述，只包含
ProofWidgets 所需信息：

```lean
structure NodePresentation where
  label : ProofWidgets.Html
  boundingShape : GraphDisplay.BoundingShape
  details? : Option ProofWidgets.Html := none

structure EdgePresentation where
  attrs : Array (String × Lean.Json) := #[]
  label? : Option ProofWidgets.Html := none
  details? : Option ProofWidgets.Html := none
```

它们不是新的图数据模型，只是构造 `GraphDisplay.Vertex` 和 `GraphDisplay.Edge` 时使用的
显示参数。

### Renderer 类型类

节点和边的数据是泛型，库不能猜测应当显示哪些字段，因此由使用者提供 renderer：

```lean
class NodeRenderer (ν : Type*) [WithData.NodeData ν] where
  id : ν → String
  render : (v : ν) → WithData.δ ν →
    Lean.MetaM NodePresentation

class EdgeRenderer (ε : Type*) [WithData.EdgeData ε] where
  render : (e : ε) → WithData.δ ε →
    Lean.MetaM EdgePresentation
```

`NodeRenderer.id` 必须为不同节点生成不同字符串。边的 `source` 和 `target` 不由
`EdgeRenderer` 提供，而是统一通过 `ep e` 和 `NodeRenderer.id` 生成。

### 统一转换入口

核心转换函数拟定为：

```lean
def graphToProps
    {ν ε : Type*}
    [DecidableEq ν] [DecidableEq ε]
    [LinearOrder ν] [LinearOrder ε]
    [WithData.NodeData ν] [WithData.EdgeData ε]
    [NodeRenderer ν] [EdgeRenderer ε]
    {ep : ε → ν × ν}
    (G : WithData.GraphWithData ep) :
    Lean.MetaM GraphDisplay.Props
```

`LinearOrder` 用于把 `Finset` 确定性地转换为 ProofWidgets 需要的数组。实现时分别遍历：

```lean
G.V.attach.sort
G.E.attach.sort
```

`attach` 保留调用 `G.data_v`、`G.data_e` 所需的成员证明；`sort` 保证每次 elaboration 都使用
稳定顺序。

转换节点时：

1. 读取 `v.val` 和 `G.data_v v`。
2. 调用 `NodeRenderer.render`。
3. 使用 `NodeRenderer.id v.val` 构造 `GraphDisplay.Vertex.id`。
4. 将结果加入 `vertices` 数组。

转换边时：

1. 读取 `e.val` 和 `G.data_e e`。
2. 计算 `(source, target) := ep e.val`。
3. 使用 `NodeRenderer.id` 生成起点和终点字符串。
4. 调用 `EdgeRenderer.render` 获得标签、详情和样式。
5. 构造 `GraphDisplay.Edge` 并加入 `edges` 数组。

### 面向命令的统一类型类

`Command.lean` 不应分析 `GraphWithData` 的全部类型参数。定义一个固定结果类型的入口：

```lean
class ToGraphDisplay (α : Type*) where
  toGraphDisplay : α → Lean.MetaM GraphDisplay.Props
```

然后为满足 renderer 和排序条件的 `GraphWithData ep` 提供通用实例，其实现调用
`graphToProps`。这样 `#show_graph` 只需要：

1. elaborate 任意 `graphExpression`。
2. 推断表达式类型 `α`。
3. 合成 `ToGraphDisplay α`。
4. 运行 `ToGraphDisplay.toGraphDisplay graphExpression`。

如果找不到实例，应给出明确错误，提示用户定义 `NodeRenderer`、`EdgeRenderer` 及所需排序
实例。

## `#show_graph` 命令

### 语法

```lean
syntax (name := showGraphCmd) "#show_graph " term : command
```

本阶段只支持能够在命令 elaboration 阶段求值的闭合表达式，例如顶层 `def` 或直接构造的图。

### Elaborator 流程

`@[command_elab showGraphCmd]` 按以下顺序工作：

1. 在 `TermElabM` 中 elaborate 图表达式并推断类型。
2. 合成该类型的 `ToGraphDisplay` 实例。
3. 构造 `ToGraphDisplay.toGraphDisplay graphExpression` 表达式。
4. 使用 `Meta.evalExpr` 将整个转换动作求值为 `MetaM GraphDisplay.Props`。
5. 在当前元编程上下文中运行该动作，得到 props。
6. 用 `<GraphDisplay ... />` 构造 `ProofWidgets.Html`。
7. 在顶层使用 `<details>` 包裹图，避免破坏 InfoView 布局。
8. 使用 `HtmlDisplayPanel` 和 `Widget.savePanelWidgetInfo` 保存当前位置的 Widget 信息。

保存 Widget 时沿用 ProofWidgets 已有模式：

```lean
Widget.savePanelWidgetInfo
  (hash HtmlDisplayPanel.javascript)
  (return json% { html : $(← Server.rpcEncode html) })
  stx
```

这里的 `stx` 是完整 `#show_graph` 命令，因此 Widget 与该命令的源码位置绑定。

## InfoView 更新机制

本阶段不维护全局可变状态。每次相关源码变化时：

1. Lean Server 使受影响的命令失效。
2. `#show_graph` 被重新 elaboration。
3. 图表达式重新求值并生成新的 props。
4. 新的 Widget 信息替换旧结果。

节点字符串 ID 应保持稳定，使 `GraphDisplay` 在 props 更新时能够识别已有节点。图表达式
暂时无法通过 elaboration 时，命令应正常报告 Lean 错误，而不是继续显示过期结果。

## ProofWidgets 使用范围

直接复用 `ProofWidgets.Component.GraphDisplay` 和 `HtmlDisplayPanel`，不修改 ProofWidgets 源码，
也不增加 JavaScript 构建流程。

当前 `GraphDisplay` 对同一对端点间的多条边支持有限，自环显示也不完善。阶段一采用以下
策略：

- `graphToProps` 检查重复的 `(source, target)`，发现后报告渲染错误。
- 示例不包含平行边和自环。
- 后端仍可保存这些结构，限制只存在于当前显示层。

## 示例接入

主示例为 `examples/example1.lean`，包含四个节点：

```text
Input → Parse → Check → Output
```

Display 和 Command 完成后，需要在该文件中：

1. 将 import 改为 `import FormattedGraph`。
2. 为 `NodeId`、`EdgeId` 定义排序实例。
3. 为 `NodeId` 定义 `NodeRenderer`。
4. 为 `EdgeId` 定义 `EdgeRenderer`。
5. 在文件末尾加入 `#show_graph exampleGraph`。

该文件是最终演示入口，不加入自环和平行边。

## 实现顺序

1. 让 `FormattedGraph.lean` 导出 `FormattedGraph.Graph`。
2. 在 `Display.lean` 中定义 presentation、renderer 和 `ToGraphDisplay`。
3. 实现并测试 `graphToProps`，暂时不写命令。
4. 使用 `example1.lean` 验证生成 4 个 vertices 和 3 个 edges。
5. 在 `Command.lean` 中实现 `#show_graph`。
6. 把示例接入 renderer 和命令，在 VS Code InfoView 中验证。
7. 让根模块导出 `Display`、`Command`，运行完整构建和测试。

## 测试方案

### 自动测试

- `lake build FormattedGraph.Graph`
- `lake build FormattedGraph.Display`
- `lake build FormattedGraph.Command`
- `lake env lean examples/example1.lean`
- 验证 props 中有 4 个节点、3 条边。
- 验证三条边的 source 和 target 正确。
- 验证节点 ID 重复时报错。
- 验证平行边时报错。
- 验证缺少 renderer 时错误信息清楚。
- 验证 `#show_graph` 所在文件能够完整 elaboration。

### InfoView 验收

1. 用 VS Code 打开 `examples/example1.lean`。
2. 将光标放在 `#show_graph exampleGraph` 上。
3. 确认显示 4 个节点和 3 条边。
4. 修改一个节点标签，确认重新 elaboration 后标签更新。
5. 添加或删除一个节点和对应边，确认图更新。
6. 确认整个流程没有读取或生成 JSON 文件。

## 完成标准

- 下游只需 `import FormattedGraph`。
- 自定义数据通过 renderer 显示，不要求修改后端 Graph。
- `#show_graph graphExpression` 能显示最终图。
- 源码修改并成功重新 elaboration 后，InfoView 更新。
- `Display.graphToProps` 可被命令之外的代码复用。
- 示例、自动测试和 InfoView 验收全部通过。
- 未实现任何阶段二 DSL 功能。
