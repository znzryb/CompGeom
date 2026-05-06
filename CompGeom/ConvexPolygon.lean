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

end CompGeom
