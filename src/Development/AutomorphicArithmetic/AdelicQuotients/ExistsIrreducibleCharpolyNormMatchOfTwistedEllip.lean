module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.exists_irreducible_charpoly_norm_match_of_twistedElliptic :
    N1 → N2 → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
        (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∀ δ : GL (Fin n) E, EllElt σ δ →
        ∃ γ : GL (Fin n) F, Irreducible (γ : Matrix (Fin n) (Fin n) F).charpoly ∧
          ∀ γ' : GL (Fin n) F, (γ' : Matrix (Fin n) (Fin n) F).charpoly = (γ : Matrix (Fin n) (Fin n) F).charpoly →
            (∃ δ' : GL (Fin n) E, normGL σ δ' = incl γ') ∧
            ∀ δ' : GL (Fin n) E, normGL σ δ' = incl γ' → ∃ h : GL (Fin n) E, δ = h⁻¹ * δ' * sigmaGL σ h := by
  intro hN1 hN2 F E _ _ _ _ _ _ σ hgen n _ δ hδ
  obtain ⟨p, hp, hpm⟩ := hδ
  have hℓ : σ ^ Module.finrank F E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank F E = 1 := by
    rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  have hc : ∀ d h : GL (Fin n) E, normGL σ (h⁻¹ * d * sigmaGL σ h) = h⁻¹ * normGL σ d * h :=
    fun d h => twNorm_twConj_of_pow_eq_one (sigmaGL σ) hθ h d
  have hreg : IsTwRegSemisimple σ δ := by
    unfold IsTwRegSemisimple
    rw [← hpm]
    exact hp.separable.map
  obtain ⟨h, γ, hγ⟩ := hN1 F E σ hgen n δ hreg
  have hv : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F E) := rfl
  have hγp : (γ : Matrix (Fin n) (Fin n) F).charpoly = p := by
    apply Polynomial.map_injective (algebraMap F E) (algebraMap F E).injective
    rw [hpm, ← Matrix.charpoly_map, ← hv, ← hγ, hc, Units.val_mul, Units.val_mul,
      Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  refine ⟨γ, hγp ▸ hp, fun γ' hγ' => ?_⟩
  have hr : IsRegSemisimple γ := by
    unfold IsRegSemisimple
    rw [hγp]; exact hp.separable
  have hr' : IsRegSemisimple γ' := by
    unfold IsRegSemisimple
    rw [hγ', hγp]; exact hp.separable
  obtain ⟨g, hg⟩ := (hN2 F E σ hgen n).2 γ γ' hr hγ'.symm
  have h0 : normGL σ ((incl g : GL (Fin n) E)⁻¹ * (h⁻¹ * δ * sigmaGL σ h) * sigmaGL σ (incl g)) = incl γ' := by
    rw [hc, hγ, hg, map_mul, map_mul, map_inv]
  refine ⟨⟨_, h0⟩, fun δ' hδ' => ?_⟩
  obtain ⟨k, hk⟩ := (hN2 F E σ hgen n).1 δ' _ γ' hr' hδ' h0
  refine ⟨k * (incl g)⁻¹ * h⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv]
  calc δ = h * incl g * ((incl g : GL (Fin n) E)⁻¹ * (h⁻¹ * δ * sigmaGL σ h) * sigmaGL σ (incl g)) *
        (sigmaGL σ (incl g))⁻¹ * (sigmaGL σ h)⁻¹ := by group
    _ = _ := by rw [hk]; group
