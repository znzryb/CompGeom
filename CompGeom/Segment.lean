/-
Copyright (c) 2026 zzy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: zzy
-/
import CompGeom.Line
import Mathlib.Analysis.Convex.Segment

/-!
# CompGeom.Segment — 闭线段（v0.1，薄包装 mathlib `segment ℝ`）

`Segment a b := segment ℝ a b`（即 mathlib 的 `[a -[ℝ] b]`）。所有标准性质都从 mathlib 复用。

新增的 compgeom-向桥接：

- `convex_segment` — mathlib 已证，这里只换个名重新导出
- `segment_subset_line` — 线段落在直线上（`signedArea` 在凸组合下消去）

下游 `Polygon` / `ConvexPolygon` 拿这两条性质就够了。
-/

open scoped Convex

namespace CompGeom

/-- 闭线段，复用 mathlib `segment ℝ a b`（同义记号 `[a -[ℝ] b]`）。 -/
def Segment (a b : Pt) : Set Pt := segment ℝ a b

@[simp]
lemma mem_segment_iff {a b p : Pt} :
    p ∈ Segment a b ↔
      ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t = 1 ∧ s • a + t • b = p := Iff.rfl

@[simp]
lemma left_mem_segment (a b : Pt) : a ∈ Segment a b := _root_.left_mem_segment ℝ a b

@[simp]
lemma right_mem_segment (a b : Pt) : b ∈ Segment a b := _root_.right_mem_segment ℝ a b

theorem convex_segment (a b : Pt) : Convex ℝ (Segment a b) := _root_.convex_segment a b

/-- **载力桥**：闭线段必落在所在直线上。

证法：把代入点 `s • a + t • b`（`s + t = 1`）展开 PiLp 加 / 数乘，再
`ring`（`s + t = 1` 让常数项归零）。这是 v0 模块化结构产生下游红利的第二例 ——
线段、直线、半平面三个独立模块由 `signedArea` 一手粘合。 -/
theorem segment_subset_line (a b : Pt) : Segment a b ⊆ Line a b := by
  intro p hp
  rcases hp with ⟨s, t, hs, ht, hst, rfl⟩
  simp only [mem_line_iff, signedArea, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have ht' : t = 1 - s := by linarith
  rw [ht']; ring

end CompGeom
