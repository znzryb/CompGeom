/-
Copyright (c) 2026 zzy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: zzy
-/
import CompGeom.Halfplane

/-!
# CompGeom.Polygon — 多边形（v0.2，最小骨架）

把多边形表示为顶点列表 `List Pt`。本模块给：

- `Polygon` —— 顶点列表的别名
- `shoelaceArea` —— **扇形三角剖分版鞋带公式**：以第一个顶点 `v₀` 为锚，对每条非邻边
  `(vᵢ, vᵢ₊₁)` 累加 `signedArea v₀ vᵢ vᵢ₊₁`。
  对凸多边形 / 简单多边形给出实际带号面积；对一般闭合多边形给出（带号）覆盖数加权和。
- 边界情形：空 / 单点 / 线段都返回 `0`；三角形 `[a, b, c]` 退化回 `signedArea a b c`。

不在这里：

- `SimplePolygon` 谓词（无自交） —— 留给 `v0.2.1`，需要 `Segment` 相交判定
- `Convex` 谓词（顶点 ccw 排列） —— 留给 `ConvexPolygon`，吃 `OrientedHalfplane` API
- 标准非扇形写法 `½ Σ (xᵢ yᵢ₊₁ − xᵢ₊₁ yᵢ)` 等价证明 —— 当下游需要时再补
-/

namespace CompGeom

/-- 多边形 = 顶点列表（顺序 = 边 = 闭合）。第一个顶点既是起点也是终点。 -/
abbrev Polygon : Type := List Pt

/-- 扇形三角剖分版鞋带面积。

递归：以 `v₀` 为扇形锚点，每次砍掉 `v₁` —— 把多边形面积分解为三角形 `(v₀, v₁, v₂)`
和剩余多边形 `[v₀, v₂, v₃, …]` 的面积之和。 -/
noncomputable def shoelaceArea : Polygon → ℝ
  | [] => 0
  | [_] => 0
  | _ :: [_] => 0
  | v0 :: v1 :: v2 :: rest => signedArea v0 v1 v2 + shoelaceArea (v0 :: v2 :: rest)

@[simp]
lemma shoelaceArea_nil : shoelaceArea ([] : Polygon) = 0 := by
  simp [shoelaceArea]

@[simp]
lemma shoelaceArea_singleton (a : Pt) : shoelaceArea ([a] : Polygon) = 0 := by
  simp [shoelaceArea]

@[simp]
lemma shoelaceArea_pair (a b : Pt) : shoelaceArea ([a, b] : Polygon) = 0 := by
  simp [shoelaceArea]

@[simp]
lemma shoelaceArea_triangle (a b c : Pt) :
    shoelaceArea ([a, b, c] : Polygon) = signedArea a b c := by
  simp [shoelaceArea]

/-- 退化三角形 `(a, a, c)` 面积为 0 —— `signedArea_self_left` 直接给。 -/
@[simp]
lemma shoelaceArea_degenerate_first_two (a c : Pt) :
    shoelaceArea ([a, a, c] : Polygon) = 0 := by
  simp

end CompGeom
