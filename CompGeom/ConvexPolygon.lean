/-
Copyright (c) 2026 zzy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: zzy
-/
import CompGeom.ConvexHull

/-!
# CompGeom.ConvexPolygon — 凸多边形 region（v0.3，最小骨架）

把"多边形所占的（闭）凸区域"刻画为顶点集的凸包：

  `convexPolygonRegion poly := convexHullPts poly`

对**真正凸**的多边形：region 恰好是其内部 + 边界。
对一般 `List Pt`：region 是顶点的凸包，凹角处会被"填平"成凸壳。

不在这里：

- `IsConvexPolygon` 谓词（顶点 ccw 排列 ∧ 无三点共线 ∧ 无自交） —— 留给 `v0.3.1`，
  需要 `signedArea` 严格符号 + `Segment` 相交判定
- 凸包的极点刻画、Carathéodory 定理 —— mathlib 已有，下游需要时引入

下游 `RotatingCalipers` / `MinAreaRect` 在 `IsConvexPolygon` 完成后才接得上。
-/

namespace CompGeom

/-- 多边形顶点表所占的（闭）凸区域 = 顶点集凸包。 -/
noncomputable def convexPolygonRegion (poly : Polygon) : Set Pt :=
  convexHullPts poly

theorem convex_convexPolygonRegion (poly : Polygon) :
    Convex ℝ (convexPolygonRegion poly) :=
  convex_convexHullPts poly

theorem vertices_subset_convexPolygonRegion (poly : Polygon) :
    (poly.toFinset : Set Pt) ⊆ convexPolygonRegion poly :=
  vertices_subset_convexHullPts poly

@[simp]
theorem convexPolygonRegion_singleton (a : Pt) :
    convexPolygonRegion [a] = ({a} : Set Pt) :=
  convexHullPts_singleton a

/-! ## IsConvexPolygon — 严格凸多边形谓词 -/

/-- 多边形顶点的 cyclic 索引：`poly.cycGet i = poly[i mod length]`，越界 wrap-around。
当 `poly.length = 0` 时返回 `(0 : Pt)` 作 fallback —— 实际使用永远不会触发，
因为 `IsConvexPolygon` 自带 `3 ≤ length` 前提。 -/
noncomputable def Polygon.cycGet (poly : Polygon) (i : ℕ) : Pt :=
  (poly[i % poly.length]?).getD 0

/-- **严格凸多边形** 谓词：

1. 顶点数 `n ≥ 3`
2. 每个相邻三元组 `(vᵢ, vᵢ₊₁, vᵢ₊₂)`（下标 cyclic mod n）都严格 ccw（`signedArea > 0`）

"严格"含义 —— `signedArea > 0`（不是 `≥ 0`），等价于：

- 每个内角严格 < 180°
- 任意三个相邻顶点不共线
- 顶点表 ccw 排列

由该条件可推出 strictly simple（无自交），因此本谓词恰好刻画 strictly convex polygon。 -/
def IsConvexPolygon (poly : Polygon) : Prop :=
  3 ≤ poly.length ∧
  ∀ i, i < poly.length →
    0 < signedArea (poly.cycGet i) (poly.cycGet (i + 1)) (poly.cycGet (i + 2))

/-- 投影：凸多边形必然有 ≥ 3 个顶点。 -/
theorem IsConvexPolygon.length_ge {poly : Polygon} (h : IsConvexPolygon poly) :
    3 ≤ poly.length := h.1

private lemma cycGet_triangle_zero (a b c : Pt) :
    Polygon.cycGet [a, b, c] 0 = a := by simp [Polygon.cycGet]

private lemma cycGet_triangle_one (a b c : Pt) :
    Polygon.cycGet [a, b, c] 1 = b := by simp [Polygon.cycGet]

private lemma cycGet_triangle_two (a b c : Pt) :
    Polygon.cycGet [a, b, c] 2 = c := by simp [Polygon.cycGet]

private lemma cycGet_triangle_three (a b c : Pt) :
    Polygon.cycGet [a, b, c] 3 = a := by simp [Polygon.cycGet]

private lemma cycGet_triangle_four (a b c : Pt) :
    Polygon.cycGet [a, b, c] 4 = b := by simp [Polygon.cycGet]

/-- ccw 三角形是凸多边形（最小构造引理）。
由 `signedArea_cyclic` 把 `(b, c, a)` / `(c, a, b)` 两个 cyclic 三元组归约回 `(a, b, c)`。 -/
theorem isConvexPolygon_of_triangle_ccw {a b c : Pt} (h : 0 < signedArea a b c) :
    IsConvexPolygon [a, b, c] := by
  refine ⟨by simp, ?_⟩
  intro i hi
  have hlen : ([a, b, c] : Polygon).length = 3 := rfl
  rw [hlen] at hi
  interval_cases i
  · -- i = 0: signedArea(cg 0, cg 1, cg 2) = signedArea(a, b, c)
    rw [show (0 + 1 : ℕ) = 1 from rfl, show (0 + 2 : ℕ) = 2 from rfl,
        cycGet_triangle_zero, cycGet_triangle_one, cycGet_triangle_two]
    exact h
  · -- i = 1: signedArea(cg 1, cg 2, cg 3) = signedArea(b, c, a) = signedArea(a, b, c)
    rw [show (1 + 1 : ℕ) = 2 from rfl, show (1 + 2 : ℕ) = 3 from rfl,
        cycGet_triangle_one, cycGet_triangle_two, cycGet_triangle_three,
        signedArea_cyclic, signedArea_cyclic]
    exact h
  · -- i = 2: signedArea(cg 2, cg 3, cg 4) = signedArea(c, a, b) = signedArea(a, b, c)
    rw [show (2 + 1 : ℕ) = 3 from rfl, show (2 + 2 : ℕ) = 4 from rfl,
        cycGet_triangle_two, cycGet_triangle_three, cycGet_triangle_four,
        signedArea_cyclic]
    exact h

end CompGeom
