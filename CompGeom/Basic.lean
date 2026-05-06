/-
Copyright (c) 2026 zzy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: zzy
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# CompGeom.Basic — 点类型与命名空间

整个库的点类型一律是 `EuclideanSpace ℝ (Fin 2)`（即 `PiLp 2 (fun _ : Fin 2 => ℝ)`），
带 Mathlib 的内积、范数、距离结构。下游模块从这里取 `Pt`。

不在这里定义任何坐标分量、向量代数原语 —— 那些都直接复用 Mathlib：

- 分量：`(p : Pt) 0`, `(p : Pt) 1`（PiLp 的 CoeFun）
- 模长平方：`‖p‖^2` / `inner ℝ p p`
- 距离：`dist p q`
-/

namespace CompGeom

/-- 二维欧氏点（带 L² 内积）。所有上层几何对象的位置都用这个类型。 -/
abbrev Pt : Type := EuclideanSpace ℝ (Fin 2)

end CompGeom
