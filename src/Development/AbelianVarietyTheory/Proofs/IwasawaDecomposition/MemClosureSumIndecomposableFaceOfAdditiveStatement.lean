module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemClosureSumIndecomposableFaceOfAdditive
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark


theorem _root_.GlobalTheory.T.mem_closure_sum_indecomposable_face_of_additive : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (∀ x y, InFace bar ψ lab β x → InFace bar ψ lab β y → InFace bar ψ lab β (x + y) ∧ ψ.evalZ (x + y) = ψ.evalZ x + ψ.evalZ y) → (∀ x, InFace bar ψ lab β x → ∃ n : ℤ, ψ.evalZ x = n) → (∀ x, InFace bar ψ lab β x → x ≠ 0 → 0 < ψ.evalZ x) → ∀ x, InFace bar ψ lab β x → x ∈ AddSubmonoid.closure {y | IsIndec bar ψ lab β y} := by
  first | exact @GlobalTheory.PolFan.Mark.mem_closure_isIndec | exact GlobalTheory.PolFan.Mark.mem_closure_isIndec | (intros; apply GlobalTheory.PolFan.Mark.mem_closure_isIndec <;> assumption)
