# formatted-graph

## Lean 版本

本项目固定使用：

```text
leanprover/lean4:v4.30.0
```

版本写在 [`lean-toolchain`](lean-toolchain) 中。

## 依赖

当前 Lake 配置安装：

- Mathlib `v4.30.0`
- Qq `v4.30.0`，Lean 元编程中常用的 quotation 辅助库

Mathlib 的 manifest 还会锁定并继承它需要的生态依赖，例如 Batteries、Cli、
Aesop、ProofWidgets 等。

## 本地部署

```bash
git clone https://github.com/longdie/formatted-graph.git
cd formatted-graph
lake update
lake exe cache get
lake build
```

`lake exe cache get` 会尽量下载 Mathlib 的预编译缓存，可以显著减少第一次
构建的时间。
