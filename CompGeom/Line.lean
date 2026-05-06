/-
Copyright (c) 2026 zzy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: zzy
-/
import CompGeom.Halfplane

/-!
# CompGeom.Line — 直线（v0.1）

通过两点 `a b` 的直线，作为 `signedArea a b · = 0` 的零集 —— 即两侧 `OrientedHalfplane`
的公共边界。当 `a ≠ b` 时是真正的几何直线；当 `a = b` 时退化成全平面（本模块不特殊处理
退化，所有引理在 `a = b` 时仍然成立）。

下游：`Segment` 模块依赖 `Line`（线段在直线上）；`Polygon`/`ConvexPolygon` 用 Line 表示边。
-/

namespace CompGeom

/-- 通过 `a b` 的直线（`signedArea` 的零集）。 -/
def Line (a b : Pt) : Set Pt := { p | signedArea a b p = 0 }

@[simp]
lemma mem_line_iff {a b p : Pt} : p ∈ Line a b ↔ signedArea a b p = 0 := Iff.rfl

@[simp]
lemma left_mem_line (a b : Pt) : a ∈ Line a b := by
  change signedArea a b a = 0
  simp [signedArea]

@[simp]
lemma right_mem_line (a b : Pt) : b ∈ Line a b := by
  change signedArea a b b = 0
  simp only [signedArea]; ring

/-- 直线 = 左右两个有向半平面的公共边界。 -/
lemma line_eq_orientedHalfplane_inter (a b : Pt) :
    Line a b = OrientedHalfplane a b ∩ OrientedHalfplane b a := by
  ext p
  simp only [Line, OrientedHalfplane, Set.mem_setOf_eq, Set.mem_inter_iff,
             signedArea_swap_ab a b p]
  constructor
  · intro h; refine ⟨?_, ?_⟩ <;> linarith
  · rintro ⟨h1, h2⟩; linarith

/-- 直线是凸集。直接复用 `convex_orientedHalfplane` + `Convex.inter`，
是 v0 基石模块产生下游红利的第一例。 -/
theorem convex_line (a b : Pt) : Convex ℝ (Line a b) := by
  rw [line_eq_orientedHalfplane_inter]
  exact (convex_orientedHalfplane a b).inter (convex_orientedHalfplane b a)

end CompGeom
