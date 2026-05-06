# CompGeom

A Lean 4 computational geometry library for competitive programming, built on
[Mathlib](https://github.com/leanprover-community/mathlib4).

> 通用 2D 计算几何脚手架。目标是「竞赛几何模板的形式化对应物」——把
> 旋转卡壳 / 凸包 / 半平面交 / 最小覆盖矩形 / 最近最远点对 等竞赛 staple 的
> 正确性给一份严格的 Lean 4 证明。**不是**为某一道题服务的 wrapper：当下
> 触发本库的 P3187 [HNOI2007] 最小矩形覆盖只是 first stress test client。

## Status

**v0** — project skeleton + foundational 2D vector algebra. Pre-1.0,
breaking changes expected as the library grows.

## Current modules

| Module | Content |
|---|---|
| `CompGeom.Vector` | 2D 向量代数：`cross` / `dot` / `normSq`，反对称、双线性、Lagrange 恒等式、Cauchy-Schwarz 二维版 |

## Design principles

1. **Built on Mathlib, not from primitives**：所有 ℝ 算术 / 实数性质 / 拓扑 / 测度
   全部走 mathlib，本库只补 mathlib **没有**的竞赛风设施
2. **`(ℝ × ℝ)` over `EuclideanSpace ℝ (Fin 2)`**：竞赛 idiom 直接、对接 .cpp
   实现轻量；mathlib 的 `EuclideanSpace` 抽象按需补转换
3. **Squared first**：所有距离 / 范数相关引理优先给 squared 版，避免
   `Real.sqrt` 的不可计算性与展开困难，sqrt 版按需单独提供
4. **不区分点和向量**：竞赛 idiom 一致；类型都是 `ℝ × ℝ`，提供 `abbrev Point`
   仅作语义标注，**不**新建强类型避免跨模块转换噪音
5. **代数核心放底层**：Lagrange 恒等式 `(a×b)² + (a·b)² = ‖a‖²‖b‖²` 是后续
   Cauchy-Schwarz / 旋转下振幅界 / sinusoid 化的共同代数源头，放在 Vector 这一档

## Roadmap

按计算几何**通用章节**展开（不绑死任何具体题目）。每条加入时机：当任意
一个 client target 需要它且 mathlib / 第三方没现成时。

### 核心几何对象

- `CompGeom.Vector` ✅ 2D 向量代数 / cross / dot / normSq / Lagrange 恒等式
- `CompGeom.Line` 直线 / 半直线 / 线段，参数化 + 一般式两套
- `CompGeom.Polygon` 包装 mathlib `Polygon (P) (n)`；`IsCcwStrictConvex` /
  `IsSimple` / 边集 / 边方向 / shoelace 面积
- `CompGeom.Rectangle` 旋转 Rectangle struct (perpendicular + parallelogram
  双约束)；坐标轴对齐特例；`area` 用 shoelace 风
- `CompGeom.Halfplane` 半平面表示与交集
- `CompGeom.Disk` 圆盘 / 圆周

### 谓词与关系

- `CompGeom.Predicates` 共线 / 同侧 / 严格内部 / 边界 / 三点叉积
  (`cross2 a b c = cross (b-a) (c-a)`)
- `CompGeom.Distance` 点点 / 点线 / 线线距离（squared 版优先）
- `CompGeom.Cover` 集合包含的几何表达；`Rectangle.covers (Polygon)` 等

### 凸性 + 高层算法

- `CompGeom.ConvexHull` Andrew 单调链 / Graham scan 算法对应的形式化谓词与构造
- `CompGeom.RotatingCalipers` 旋转卡壳通用 framework（直径 / 最小外接矩形 /
  最小宽度等共用）
- `CompGeom.Trig.Sinusoid` 旋转下 dot 乘积的 sinusoid 化与振幅界——对任意两
  向量 u, v 和旋转角 θ，`(u rotated by θ) · v` 的振幅刻画。**这条是旋转卡壳
  所有变体证明的代数核心**

## Examples / Client projects

每个 client 在自己的 dir 通过 `lake require` 引 CompGeom，再写题目特定证明。
本仓库**不**收 client 代码。

- **P3187 [HNOI2007] 最小矩形覆盖** — first stress test client；目标定理：
  覆盖凸包的最小面积矩形至少有一条边和凸包某条边共线（Toussaint 1983 路）
- 候选未来 client（按可行性排序）：
  1. 凸多边形直径（QOJ 784） — 验证 ConvexHull + RotatingCalipers
  2. 最远点对 — 同上
  3. 半平面交可行性 — 验证 Halfplane
  4. Welzl 最小圆覆盖 — 验证 Disk + 随机增量算法骨架
  5. Andrew 单调链构造正确性 — 验证 ConvexHull 自身

## Usage

In your downstream `lakefile.toml`:

```toml
[[require]]
name = "CompGeom"
git = "https://github.com/znzryb/CompGeom"
rev = "main"
```

Then:

```lean
import CompGeom              -- 全部模块
-- 或按需
import CompGeom.Vector
```

Note: integration patterns (`lake require` from problem dirs vs.
`LEAN_PATH` injection) will be validated as the first downstream client lands;
expect the recipe above to evolve once we hit real-world friction.

## Mathlib pin policy

Currently pinned to **mathlib v4.29.1**. When upgrading mathlib upstream, this
library bumps in lockstep. The Lean toolchain (`lean-toolchain` file) and the
mathlib `rev` in `lakefile.toml` are kept consistent.

## License

[Apache 2.0](LICENSE) — matches the Mathlib ecosystem mainstream choice
(formal-conjectures, Pick's Theorem formalization, Rupert.lean all use it).

## Acknowledgments

- [Mathlib](https://github.com/leanprover-community/mathlib4) — foundation
  layer (real analysis, convex sets, `Polygon` skeleton)
- [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  `Geometry/2d.lean` — `IsCcwConvexPolygon` / `triangle_area` 模式参考
- [Dronmong/Formalizing-Pick-s-Theorem-in-Lean](https://github.com/Dronmong/Formalizing-Pick-s-Theorem-in-Lean)
  — Lean 4 唯一显式 shoelace polyArea 参考实现
- [dwrensha/Rupert.lean](https://github.com/dwrensha/Rupert) — Lean 4 2D
  geometry idiom 风格参考
