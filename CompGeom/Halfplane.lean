/-
Copyright (c) 2026 zzy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: zzy
-/
import CompGeom.Basic
import Mathlib.Analysis.Convex.Basic

/-!
# CompGeom.Halfplane — 有向半平面（v0 基石模块）

本模块给出 compgeom 库的第一个非平凡内容：

- `signedArea a b c` — 有向三角形 `(a, b, c)` 的两倍带号面积；正：ccw，负：cw，零：共线。
- `OrientedHalfplane a b` — 有向直线 `a → b` 的左闭半平面（含直线本身）。
- `convex_orientedHalfplane` — 与 Mathlib `Convex ℝ` 的桥接，下游凸性证明的复用模板。

下游模块（`Line` / `Polygon` / `ConvexPolygon` / `ConvexHull` / `RotatingCalipers`）
都建在这三件事上 —— 比如 "凸包是半平面交"、"多边形顶点 ccw 排列" 这些命题，
原始定义就要走 `signedArea` / `OrientedHalfplane`。
-/

namespace CompGeom

/-- 有向三角形 `(a, b, c)` 的两倍带号面积。

走 `(b - a) × (c - a)` 的二维叉积形式（再除 2）：
- `> 0` ⇔ `c` 位于有向直线 `a → b` 的左侧（逆时针）
- `< 0` ⇔ 右侧（顺时针）
- `= 0` ⇔ 三点共线 -/
noncomputable def signedArea (a b c : Pt) : ℝ :=
  ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) / 2

/-- 有向直线 `a → b` 的左闭半平面（边界包含直线本身）。

定义为 `{p | 0 ≤ signedArea a b p}`，即 `signedArea` 的非负下水平集。 -/
def OrientedHalfplane (a b : Pt) : Set Pt :=
  { p | 0 ≤ signedArea a b p }

@[simp]
lemma signedArea_self_left (a c : Pt) : signedArea a a c = 0 := by
  simp [signedArea]

lemma signedArea_swap_ab (a b c : Pt) : signedArea a b c = - signedArea b a c := by
  simp only [signedArea]; ring

@[simp]
lemma mem_orientedHalfplane_iff {a b p : Pt} :
    p ∈ OrientedHalfplane a b ↔ 0 ≤ signedArea a b p :=
  Iff.rfl

/-- 把 `p ↦ signedArea a b p` 显式表为仿射映射 `Pt →ᵃ[ℝ] ℝ`。

线性部分：`v ↦ ((b 0 - a 0) * v 1 - (b 1 - a 1) * v 0) / 2` —— 平移 `a → 0` 后的二维叉积。

是 `convex_orientedHalfplane` 的桥：把 `OrientedHalfplane` 写成 `Set.Ici 0` 沿这个仿射映射的拉回，
凸性由 `Convex.affine_preimage` 直接得到。 -/
noncomputable def signedAreaAffine (a b : Pt) : Pt →ᵃ[ℝ] ℝ where
  toFun p := signedArea a b p
  linear :=
    { toFun v := ((b 0 - a 0) * v 1 - (b 1 - a 1) * v 0) / 2
      map_add' := fun u v => by
        simp only [PiLp.add_apply]; ring
      map_smul' := fun c v => by
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_vadd' p v := by
    change signedArea a b (v + p) =
      ((b 0 - a 0) * v 1 - (b 1 - a 1) * v 0) / 2 + signedArea a b p
    simp only [signedArea, PiLp.add_apply]; ring

@[simp]
lemma signedAreaAffine_apply (a b p : Pt) :
    signedAreaAffine a b p = signedArea a b p := rfl

/-- **载力定理**：有向半平面是 Mathlib 意义下的凸集。

证法：把 `OrientedHalfplane a b` 写成 `signedAreaAffine a b` 沿 `Set.Ici 0` 的拉回，再调
`Convex.affine_preimage` —— 把"半平面是凸集"这个 compgeom 原始命题彻底规约到 Mathlib
现成 API 里"线段/光线/水平集是凸集"的标准事实。

下游一切凸性证明都从这里复用 —— 比如多边形是凸的当且仅当它是若干 `OrientedHalfplane` 的交，
而交一保凸（`Convex.inter`）。 -/
theorem convex_orientedHalfplane (a b : Pt) :
    Convex ℝ (OrientedHalfplane a b) := by
  have h : OrientedHalfplane a b = signedAreaAffine a b ⁻¹' Set.Ici (0 : ℝ) := by
    ext p; simp [OrientedHalfplane]
  rw [h]
  exact (convex_Ici (0 : ℝ)).affine_preimage (signedAreaAffine a b)

end CompGeom
