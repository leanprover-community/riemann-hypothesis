module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.InstMainA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne.ConjDual

theorem valuation_lt_one_iff {Ω : Type} [Field Ω] {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω)
    (hA : ∀ y, y ∈ A ↔ c y ∈ A') (y : Ω) : A.valuation y < 1 ↔ A'.valuation (c y) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, hA, map_inv₀,
    EmbeddingLike.map_eq_zero_iff]

theorem tame_dual {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {a : WDRep h V}
    (ha : a.Tame) : a.dual.Tame := by
  intro σ hσ
  have h1 : a.ρ σ⁻¹ = 1 := ha σ⁻¹ ((Wild E A).inv_mem hσ)
  rw [WDRep.dual_ρ, h1]
  ext
  simp

theorem transport_dual {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)}
    {h : IsPlaceOver A w} {h' : IsPlaceOver A' w'} (s : E → E) (c : Ω ≃+* Ω)
    (hc : ∀ x : E, c (algebraMap E Ω x) = algebraMap E Ω (s x))
    (hA : ∀ y, y ∈ A ↔ c y ∈ A') (x : WD h) (x' : WD h') (n : ℕ)
    (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ))
    (hb : WD.mk b = x.lpDual) (hb' : WD.mk b' = x') (hN : b.N = b'.N)
    (hρ : ∀ (τ : Weil h) (τ' : Weil h'),
      (∀ z, c ((τ : G E Ω) z) = (τ' : G E Ω) (c z)) → b.ρ τ = b'.ρ τ') :
    (x.mono0 → x'.mono0) ∧ x'.lpDim = x.lpDim ∧ (x.tame → x'.tame) := by
  subst hb'
  induction x using WD.ind with
  | hP m a =>
    rw [WD.lpDual_mk] at hb
    refine ⟨fun h0 => ?_, ?_, fun h0 => ?_⟩
    · rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0 ⊢
      rw [← hN, ← WD.monodromyZero_ofWeilDeligneRepClass_iff, hb, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.dual_N, h0]
      ext
      simp
    · have h1 := congrArg WD.lpDim hb
      rw [WD.lpDim_mk, WD.lpDim_mk, Subspace.dual_finrank_eq] at h1
      rw [WD.lpDim_mk, WD.lpDim_mk, h1]
    · rw [WD.tame_mk] at h0 ⊢
      have h1 : b.Tame := by
        rw [← WD.tame_mk, hb, WD.tame_mk]
        exact tame_dual h0
      intro τ' hτ'
      let σ : G E Ω :=
        { (c.trans ((τ' : G E Ω) : Ω ≃+* Ω)).trans c.symm with
          commutes' := fun r => by
            show c.symm ((τ' : G E Ω) (c (algebraMap E Ω r))) = _
            rw [hc, AlgEquiv.commutes, ← hc, RingEquiv.symm_apply_apply] }
      have hσ : ∀ z, c (σ z) = (τ' : G E Ω) (c z) := fun z => c.apply_symm_apply _
      have hw : σ ∈ Wild E A := fun y hy => by
        rw [valuation_lt_one_iff c hA, map_sub, map_div₀, map_one, hσ]
        exact hτ' _ ((_root_.map_ne_zero c).2 hy)
      rw [← hρ ⟨σ, Ine_le_Weil h (Wild_le_Ine hw)⟩ τ' hσ]
      exact h1 _ hw

theorem mono_dim_wild : ∀ (D : D7) (w w' : PlE D.host) (c : D.nd.Om ≃+* D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) →
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') →
    ∀ (x : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w)) (x' : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w')) (n : ℕ)
      (b : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w) (Fin n → ℂ)) (b' : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w') (Fin n → ℂ)),
    GlobalTheory.WeilDeligne.WD.mk b = x.lpDual → GlobalTheory.WeilDeligne.WD.mk b' = x' → b.N = b'.N →
    (∀ (τ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w)) (τ' : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w')),
        (∀ z, c ((τ : GE D.nd) z) = (τ' : GE D.nd) (c z)) → b.ρ τ = b'.ρ τ') →
    (x.mono0 → x'.mono0) ∧ x'.lpDim = x.lpDim ∧
    ((∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), σ ∈ wildSet D.nd (D.nd.plOm.1 w) → x.inePol σ = (X - 1) ^ x.lpDim) →
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w'), σ ∈ wildSet D.nd (D.nd.plOm.1 w') → x'.inePol σ = (X - 1) ^ x'.lpDim) := by
  intro D w w' c hc hA x x' n b b' hb hb' hN hρ
  obtain ⟨h1, h2, h3⟩ := transport_dual (fun y => D.host.conj y) c hc hA x x' n b b' hb hb' hN hρ
  refine ⟨h1, h2, fun H σ _ hσ => ?_⟩
  exact (WD.tame_iff_inePol x').mp (h3 ((WD.tame_iff_inePol x).mpr
    fun τ hτ => H τ (Wild_le_Ine hτ) hτ)) σ hσ

end GlobalTheory.WeilDeligne.ConjDual
