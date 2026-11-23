module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDifferentialAdjointCupProductPairing
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
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap

@[expose] public section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.cechDifferential_adjoint_cupProductPairing : ∀ (k : Type) [Field k] (d : ℕ) (E : Type) [AddCommGroup E] [Module k E] (E' : Type) [AddCommGroup E'] [Module k E'] (A : Finset (Fin (d + 1)) → Submodule k E) (B : Finset (Fin (d + 1)) → Submodule k E') (β : E →ₗ[k] E' →ₗ[k] k), (∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) → (∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t) → (∀ i, (Finset.univ.erase i).Nonempty → ∀ a ∈ A (Finset.univ.erase i), ∀ b ∈ B (Finset.univ.erase i), β a b = 0) → Adj (cech A) (cech B) (cupPair β) d := by
  first | (exact @GlobalTheory.PD.CupAdj.cech_adj) | (exact GlobalTheory.PD.CupAdj.cech_adj) | (intros; apply GlobalTheory.PD.CupAdj.cech_adj  <;> assumption)
