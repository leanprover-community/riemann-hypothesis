module

public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexEqOfSelfDualAlternating
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Formalism.HermitianLattices.StatementJac
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

theorem _root_.GlobalTheory.T.relIndex_eq_of_selfDual_alternating : ∀ (H : Type) [AddCommGroup H] (ω : H → H → ℝ) (Λ₁ Λ₂ : AddSubgroup H), (∀ x y z, ω (x + y) z = ω x z + ω y z) → (∀ x y, ω x y = -ω y x) → (∀ x, x ∈ Λ₁ ↔ ∀ y ∈ Λ₁, ∃ n : ℤ, ω x y = n) → (∀ x, x ∈ Λ₂ ↔ ∀ y ∈ Λ₂, ∃ n : ℤ, ω x y = n) → Λ₁.relIndex Λ₂ ≠ 0 → Λ₂.relIndex Λ₁ ≠ 0 → Λ₁.relIndex Λ₂ = Λ₂.relIndex Λ₁ := by
  first | exact @GlobalTheory.MomT.DualCount.relIndex_eq_of_selfDual | exact GlobalTheory.MomT.DualCount.relIndex_eq_of_selfDual | (intros; apply GlobalTheory.MomT.DualCount.relIndex_eq_of_selfDual <;> assumption)
