module

public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContCohomologyTransportMulEquiv
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
import Formalism.GaloisCohomology.StatementLoc

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

theorem _root_.GlobalTheory.T.nonempty_H1_H2_equiv_of_continuous_mulEquiv : ∀ (R : Type) [CommRing R] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (e : Γ' ≃* Γ), Continuous e → Continuous e.symm → ∀ (ρ : Representation R Γ M) (ρ' : Representation R Γ' M), (∀ g m, ρ' g m = ρ (e g) m) → Nonempty (H1 ρ ≃ H1 ρ') ∧ Nonempty (H2 ρ ≃ H2 ρ') ∧ (Subsingleton (Hn ρ 3) → Subsingleton (Hn ρ' 3)) := by
  first | exact @GlobalTheory.contCohomology_transport_mulEquiv | exact GlobalTheory.contCohomology_transport_mulEquiv | (intros; apply GlobalTheory.contCohomology_transport_mulEquiv <;> assumption)
