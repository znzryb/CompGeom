/-
Copyright (c) 2026 zzy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: zzy
-/
import CompGeom.Polygon
import Mathlib.Analysis.Convex.Hull

/-!
# CompGeom.ConvexHull — 有限点集凸包（v0.3，薄包装 mathlib `convexHull`）

`convexHullPts verts := convexHull ℝ (verts.toFinset : Set Pt)` ——
把 mathlib 的通用 `convexHull` 应用到 `List Pt` 上的便利包装。

下游 `ConvexPolygon` 的 region 直接用这个；`Hull` 算法（Graham Scan / Andrew Monotone Chain）
归约到此凸包的等价刻画。

mathlib 已证 / 复用：

- `convex_convexHull` — 凸包是凸的
- `subset_convexHull` — 原集合 ⊆ 凸包
- `convexHull_mono` — 单调
- `convexHull_singleton` — `{x}` 凸包是 `{x}`
-/

namespace CompGeom

/-- 顶点列表的凸包：先去重成 `Finset`，再取 mathlib `convexHull ℝ`。 -/
noncomputable def convexHullPts (verts : List Pt) : Set Pt :=
  convexHull ℝ (verts.toFinset : Set Pt)

theorem convex_convexHullPts (verts : List Pt) :
    Convex ℝ (convexHullPts verts) :=
  convex_convexHull ℝ _

theorem vertices_subset_convexHullPts (verts : List Pt) :
    (verts.toFinset : Set Pt) ⊆ convexHullPts verts :=
  subset_convexHull ℝ _

@[simp]
theorem convexHullPts_singleton (a : Pt) :
    convexHullPts [a] = ({a} : Set Pt) := by
  simp [convexHullPts, convexHull_singleton]

/-- 顶点序变化不影响凸包（凸包只看点集，不看序）—— 用 `toFinset` 化掉序信息。 -/
theorem convexHullPts_perm {verts₁ verts₂ : List Pt}
    (h : verts₁.toFinset = verts₂.toFinset) :
    convexHullPts verts₁ = convexHullPts verts₂ := by
  simp [convexHullPts, h]

/-- 顶点子集 ⇒ 凸包子集。 -/
theorem convexHullPts_mono {verts₁ verts₂ : List Pt}
    (h : verts₁.toFinset ⊆ verts₂.toFinset) :
    convexHullPts verts₁ ⊆ convexHullPts verts₂ :=
  convexHull_mono (Finset.coe_subset.mpr h)

end CompGeom
