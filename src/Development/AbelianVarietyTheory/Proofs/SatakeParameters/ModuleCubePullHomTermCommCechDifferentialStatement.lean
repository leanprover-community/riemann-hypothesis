module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechAbPullApp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModuleCubePullHomTermCommCechDifferential
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

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull

theorem _root_.GlobalTheory.T.moduleCubePullHom_term_comm_cechDifferential : ∀ {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R S : Type} [Ring R] [Ring S]
    {σ : R →+* S} {τ : κ → ι} {A : Cube.{0} ι R} {B : Cube.{0} κ S}
    (ψ : Cube.PullHom σ τ A B) (p : ℕ) (x : Cube.Term A p),
    ψ.term (p + 1) (Cube.d A p x) = Cube.d B p (ψ.term p x) := by
  first | (exact @GlobalTheory.Cube.PullHom.term_d) | (exact GlobalTheory.Cube.PullHom.term_d) | (intros; apply GlobalTheory.Cube.PullHom.term_d  <;> assumption)
