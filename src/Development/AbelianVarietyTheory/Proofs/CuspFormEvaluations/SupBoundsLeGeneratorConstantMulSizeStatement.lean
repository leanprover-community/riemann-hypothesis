module

public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupBoundsLeGeneratorConstantMulSize
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.QuotientParamNonneg

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.supBounds_le_generatorConstant_mul_size : ∀ (D : D7) (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j) (p : ℕ), 2 ≤ large₂.sc.L → 0 < w.n → (140 * D.R.r * large₂.sc.L * absA w + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L ≤ 400 * Zb D large₂ * w.size) ∧ (2 * (lamStar D + 2 * Real.log p) * w.size + 400 * Zb D large₂ * w.size + lamStar D * w.size ≤ WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) p * w.size) ∧ ((lamStar D + 2 * Real.log p) * w.size + (400 * Zb D large₂ * w.size + 3 * D.R.f * D.R.r * w.n * large₂.sc.L + 5 * Real.log (Module.finrank ℚ B.KO) + Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO + 2) ≤ WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) p * w.size) := by
  first | exact @GlobalTheory.RunIn.sup_bounds_le_Gc | exact GlobalTheory.RunIn.sup_bounds_le_Gc | (intros; apply GlobalTheory.RunIn.sup_bounds_le_Gc <;> assumption)
