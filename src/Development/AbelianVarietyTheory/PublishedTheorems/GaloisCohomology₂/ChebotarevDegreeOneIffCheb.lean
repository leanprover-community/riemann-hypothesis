module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Published

def ChebotarevDegreeOne : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (L : IntermediateField F Ω) [FiniteDimensional F L] [IsGalois F L] (g : L ≃ₐ[F] L)
    (S : Set (HeightOneSpectrum (𝓞 F))), S.Finite →
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧
      ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Ine (F := F) B ≤ L.fixingSubgroup ∧
        ∃ σ : G F Ω, IsFrob B (normV v) σ ∧ AlgEquiv.restrictNormalHom L σ = g

theorem chebotarevDegreeOne_iff_cheb : ChebotarevDegreeOne ↔ GlobalTheory.TwSys.Cheb := by
  classical
  constructor
  · intro h F Ω _ _ _ _ _ U hU hN g A
    have : IsGalois F Ω := {}
    let U' : ClosedSubgroup (G F Ω) := ⟨U, U.isClosed_of_isOpen hU⟩
    have hfix : (IntermediateField.fixedField U).fixingSubgroup = U :=
      InfiniteGalois.fixingSubgroup_fixedField U'
    have : FiniteDimensional F (IntermediateField.fixedField U) :=
      (InfiniteGalois.isOpen_iff_finite _).1 (by rw [hfix]; exact hU)
    have : IsGalois F (IntermediateField.fixedField U) :=
      (InfiniteGalois.normal_iff_isGalois _).1 (by rw [hfix]; exact hN)
    have hfin := (GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).2
    obtain ⟨v, hv, hd, B, hB, hI, σ, hσ, hg⟩ := h F Ω (IntermediateField.fixedField U)
      (AlgEquiv.restrictNormalHom _ g) _ (A.finite_toSet.union hfin)
    simp only [Set.mem_union, Finset.mem_coe, not_or] at hv
    refine ⟨v, hv.1, hd, by simpa using hv.2, B, hB, hfix ▸ hI, σ, hσ, ?_⟩
    rw [← hfix, ← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, hg, map_inv,
      mul_inv_cancel]
  · intro h F Ω _ _ _ _ _ L _ _ g S hS
    have : IsGalois F Ω := {}
    obtain ⟨g', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L) Ω g
    obtain ⟨v, hv, hd, -, B, hB, hI, σ, hσ, hg⟩ := h F Ω L.fixingSubgroup
      (IntermediateField.fixingSubgroup_isOpen L) ((InfiniteGalois.normal_iff_isGalois L).2 inferInstance) g'
      hS.toFinset
    refine ⟨v, by simpa using hv, hd, B, hB, hI, σ, hσ, ?_⟩
    rwa [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv,
      mul_inv_eq_one] at hg

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem ChebotarevDegreeOne.dense (h : ChebotarevDegreeOne) {S : Set (HeightOneSpectrum (𝓞 F))} (hS : S.Finite) :
    Dense {σ : G F Ω | ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧
      ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ IsFrob B (normV v) σ} := by
  rw [dense_iff_inter_open]
  rintro W hW ⟨g, hg⟩
  have hV : IsOpen {s : G F Ω | s * g ∈ W} := hW.preimage (continuous_mul_const g)
  have : IsGalois F Ω := {}
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV (by simpa using hg)
  obtain ⟨v, hv, hd, -, B, hB, -, σ, hσ, hU'⟩ := chebotarevDegreeOne_iff_cheb.1 h F Ω U.toSubgroup U.isOpen
    U.isNormal' g hS.toFinset
  exact ⟨σ, by simpa using hU hU', v, by simpa using hv, hd, B, hB, hσ⟩

theorem ChebotarevDegreeOne.eq_of_frob (h : ChebotarevDegreeOne) {S : Set (HeightOneSpectrum (𝓞 F))}
    (hS : S.Finite) {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f f' : G F Ω → Y} (hf : Continuous f)
    (hf' : Continuous f')
    (he : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v.asIdeal.inertiaDeg ℤ = 1 → ∀ B : ValuationSubring Ω,
      IsPlaceOver B v → ∀ σ, IsFrob B (normV v) σ → f σ = f' σ) : f = f' :=
  Continuous.ext_on (h.dense hS) hf hf' fun σ ⟨v, hv, hd, B, hB, hσ⟩ => he v hv hd B hB σ hσ

end GlobalTheory.Published

end
