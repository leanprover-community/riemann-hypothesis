module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocResidueFrac
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartScalingIndep
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocResidueAdjoin
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocRankAdjoin
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem SemilocResidueAdjoin.isMultiHomogIdeal_map {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {R : Type} [CommRing R] (φ : ℤ →+* R) {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    IsMultiHomogIdeal (P.map (MvPolynomial.map φ : MRing ι →+* MRingOver R ι)) := by
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨MvPolynomial.map φ '' S, ?_, Ideal.map_span _ _⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, fun m hm => ha m (MvPolynomial.support_map_subset _ _ hm)⟩

theorem SemilocResidueAdjoin.exists_int_mul {σ F : Type} [Field F]
    (hF : ∀ c : F, ∃ a b : ℤ, (b : F) ≠ 0 ∧ c = a / b) (f : MvPolynomial σ F) :
    ∃ (g : MvPolynomial σ ℤ) (d : ℤ), (d : F) ≠ 0 ∧ C (d : F) * f = MvPolynomial.map (Int.castRingHom F) g := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    obtain ⟨a, b, hb, rfl⟩ := hF c
    refine ⟨C a, b, hb, ?_⟩
    rw [map_C, ← C_mul, mul_div_cancel₀ _ hb, eq_intCast]
  | add f g hf hg =>
    obtain ⟨g₁, d₁, h₁, e₁⟩ := hf
    obtain ⟨g₂, d₂, h₂, e₂⟩ := hg
    refine ⟨C d₂ * g₁ + C d₁ * g₂, d₁ * d₂, by push_cast; exact mul_ne_zero h₁ h₂, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_C, map_C, ← e₁, ← e₂, eq_intCast, eq_intCast]
    push_cast
    rw [C_mul]
    ring
  | mul_X f q hf =>
    obtain ⟨g, d, h, e⟩ := hf
    exact ⟨g * X q, d, h, by rw [map_mul, map_X, ← e, mul_assoc]⟩

theorem SemilocResidueAdjoin.isMultiHomogIdeal_ker {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (hF : ∀ c : F, ∃ a b : ℤ, (b : F) ≠ 0 ∧ c = a / b)
    (x : (Σ k, ι k) → Ω) (hmh : IsMultiHomogIdeal (RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω))) :
    IsMultiHomogIdeal (RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω)) := by
  have e : ∀ g : MRing ι, aeval x (MvPolynomial.map (Int.castRingHom F) g) = aeval x g := fun g => by
    rw [← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
  suffices h : RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω) =
      (RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω)).map (MvPolynomial.map (Int.castRingHom F)) by
    rw [h]
    exact SemilocResidueAdjoin.isMultiHomogIdeal_map _ hmh
  refine le_antisymm (fun f hf => ?_) (Ideal.map_le_iff_le_comap.2 fun g hg => ?_)
  · obtain ⟨g, d, hd, hg⟩ := SemilocResidueAdjoin.exists_int_mul hF f
    have hg0 : g ∈ RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) := by
      rw [RingHom.mem_ker, ← e, ← hg, map_mul, (RingHom.mem_ker).1 hf, mul_zero]
    have hf' : f = C (d : F)⁻¹ * MvPolynomial.map (Int.castRingHom F) g := by
      rw [← hg, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hd, C_1, one_mul]
    rw [hf']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hg0)
  · rw [Ideal.mem_comap, RingHom.mem_ker, e]
    exact hg

theorem SemilocResidueAdjoin.proof (hR : SemilocResidueFrac.Statement) (hT : ChartScalingIndep.Statement) :
    SemilocResidueAdjoin.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hZ hs hsP hW W' hW' _ G' i' hi'
  let F := (⊥ : Subfield G'.Φ)
  have hF : ∀ c : F, ∃ a b : ℤ, (b : F) ≠ 0 ∧ c = a / b := primeSubfield_exists_div
  have hx : ∀ k', G'.x' ⟨k', i' k'⟩ ≠ 0 := fun k' h => hi' k' (by
    rw [← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_X, h])
  have hmh := SemilocResidueAdjoin.isMultiHomogIdeal_ker hF G'.x' (by rw [G'.genericFibre_ker_target]; exact hW'.1.2.1)
  rw [hR K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW W' hW' G' i' hi' F hF,
    SemilocRankAdjoin.chain hT G' i' F hv hx hmh]

end GroundTheory.Heights₂.Heights.Inter
