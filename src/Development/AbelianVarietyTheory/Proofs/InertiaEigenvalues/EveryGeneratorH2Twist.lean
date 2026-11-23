module

public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCyclotomicCharacterLocalGaloisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2QuotientFiniteCardStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiInjectiveQuotientH2Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.FunctorialityH2

theorem bijective_phi_quot_pow : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) → ∀ k : ℕ, Function.Bijective (phi ε z (O ⧸ IsLocalRing.maximalIdeal O ^ k)) := by
  intro p _ K O _ _ _ _ _ G _ _ hT hK hO i ε hε z hz k
  haveI : ContinuousMul G := ⟨by
    have h : (fun q : G × G => q.1 * q.2) = fun q => i.symm (i q.1 * i q.2) := by
      funext q; simp
    rw [h]
    exact i.symm.continuous.comp
      ((i.continuous.comp continuous_fst).mul (i.continuous.comp continuous_snd))⟩
  have hinj := GlobalTheory.T.phi_injective_quotient_H2 hO (GlobalTheory.T.continuous_cyclotomic_character_localGalois hO i hε) z hz k
  obtain ⟨_, hcard⟩ := GlobalTheory.T.finite_H2_twist_quotient_pow_and_card_le hT hK hO i hε k
  exact hinj.bijective_of_nat_card_le hcard

end GlobalTheory.FunctorialityH2
