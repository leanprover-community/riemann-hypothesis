module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductLeadingTerm
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory GlobalTheory.DI

theorem _root_.GlobalTheory.T.cechAntisymmetrizedCupProduct_leading_term : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (j : ι), alt f h a v {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k))) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) (j : ι) (γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V), IsPhi p f h Φ → IsGamma p (f j) γ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, Φ x {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x := by
  first | exact @GlobalTheory.DI.PhiLead.leading_term | exact GlobalTheory.DI.PhiLead.leading_term | (intros; apply GlobalTheory.DI.PhiLead.leading_term <;> assumption)
