module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Local

variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  {Y : Model Xo' c' (c'.V W).subtype} {r : Xo'.XF c' ⟶ Xo.XF c} {ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)}
  {hle : c.F ≤ c'.F} {r₀ : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
  {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} [Fact p.Prime] {Xw : Y.X.Opens}

theorem exists_unit (hG : GenSt) (hL : Laws U x) (s : ArchSec U x Z (flatWt Dw τ)) (hc : IsCover Y r hle Z la p Xw)
    {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {ξ : Sp R ⟶ Y.X} [IsOpenImmersion ξ] {β : c'.V W →+* R}
    (hβ : ξ ≫ Y.s = spMap β) (hξ : ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Xw) {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)} (he : IsTanBasis Y.t ξ e) {U₁ U₂ : Fin g → Fin g → R}
    (h₁ : EigFam Y.t ξ (β.comp (embV c' W τ.1)) e U₁) (h₂ : EigFam Y.t ξ (β.comp (embV c' W (conjEmb τ.1))) e U₂)
    (K₁ : Fin (Dw.mult τ.1) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g) (a₁ : Fin (Dw.mult τ.1) → Fin g → R)
    (a₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → R) (ε : ℤˣ) :
    ∃ u : (Localization.Away ((p : R) * (pairDet a₁ (U₁ ∘ K₁) * pairDet a₂ (U₂ ∘ K₂))))ˣ,
      ∀ (k : Type) [Field k] [Algebra c.F k] (ψ : Localization.Away ((p : R) * (pairDet a₁ (U₁ ∘ K₁) * pairDet a₂ (U₂ ∘ K₂))) →+* k) (yy : Sp k ⟶ Xo'.XF c'),
        yy ≫ Y.j = spMap (ψ.comp (algebraMap R _)) ≫ ξ → ∃ fv : k,
          GVal Y r ν τ.1 s.sig yy (bcV Y.t (ψ.comp (algebraMap R _)) e) (fun i b => ψ (algebraMap R _ (U₁ (K₁ i) b)))
            (fun i b => ψ (algebraMap R _ (U₂ (K₂ i) b))) fv ∧
          ψ u = fv * ((ε : ℤ) : k) * ψ (algebraMap R _ (pairDet a₁ (U₁ ∘ K₁))) / ψ (algebraMap R _ (pairDet a₂ (U₂ ∘ K₂))) := by
  set q : R := (p : R) * (pairDet a₁ (U₁ ∘ K₁) * pairDet a₂ (U₂ ∘ K₂)) with hq
  have hu : IsUnit (algebraMap R (Localization.Away q) q) := IsLocalization.Away.algebraMap_isUnit q
  by_cases h0 : q = 0
  · refine ⟨1, fun k _ _ ψ _ _ => ?_⟩
    have := hu.map ψ
    rw [show algebraMap R (Localization.Away q) q = 0 from (congrArg _ h0).trans (map_zero _), map_zero] at this
    exact absurd this not_isUnit_zero
  have hle' : Submonoid.powers q ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors h0
  haveI : IsDomain (Localization.Away q) := IsLocalization.isDomain_localization hle'
  haveI : IsIntegrallyClosed (Localization.Away q) := isIntegrallyClosed_of_isLocalization _ _ hle'
  have hinj : Function.Injective (algebraMap R (Localization.Away q)) := IsLocalization.injective _ hle'
  let ρ := algebraMap R (Localization.Away q)
  have hu' : IsUnit ((p : Localization.Away q) * (ρ (pairDet a₁ (U₁ ∘ K₁)) * ρ (pairDet a₂ (U₂ ∘ K₂)))) := by
    rw [← map_natCast ρ, ← map_mul, ← map_mul]; exact hu
  have u₁ := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right hu')
  have u₂ := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hu')
  have mp : ∀ {m : ℕ} (a V : Fin m → Fin g → R), ρ (pairDet a V) = pairDet (fun i b => ρ (a i b)) fun i b => ρ (V i b) :=
    fun a V => by
      rw [pairDet, pairDet, RingHom.map_det]
      congr 1
      ext i j

      simp [map_sum]
  haveI : IsOpenImmersion (spMap ρ) := IsOpenImmersion.of_isLocalization q
  obtain ⟨f, hf⟩ := hG E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw Fact.out hc (Localization.Away q)
    (spMap ρ ≫ ξ) (ρ.comp β) inferInstance (by rw [Category.assoc, hβ, spMap_spMap]) (isUnit_of_mul_isUnit_left hu')
    (by rw [bot_map hinj]; exact hξ) g (bcV Y.t ρ e) (fun i b => ρ (U₁ (K₁ i) b)) (fun i b => ρ (a₁ i b))
    (fun i b => ρ (U₂ (K₂ i) b)) (fun i b => ρ (a₂ i b)) (isTanBasis_bc he ρ)
    (fun S _ φ => by
      rw [sp_sp, bcV_bcV]
      exact ⟨fun i => (h₁ S (φ.comp ρ)).1 (K₁ i), fun i => (h₂ S (φ.comp ρ)).1 (K₂ i)⟩)
    (mp a₁ _ ▸ u₁) (mp a₂ _ ▸ u₂)
  refine ⟨f * Units.map (Int.castRingHom _).toMonoidHom ε * u₁.unit * u₂.unit⁻¹, fun k _ _ ψ yy hy => ⟨ψ f, ?_, ?_⟩⟩
  · have := hf k ψ yy (by rw [sp_sp]; exact hy)
    rwa [bcV_bcV] at this
  · rw [eq_div_iff (u₂.map ψ).ne_zero, ← map_mul]
    change ψ (_ * (u₂.unit : Localization.Away q)) = _
    rw [← Units.val_mul, inv_mul_cancel_right]
    simp [ρ]

end Local


variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  {Y : Model Xo' c' (c'.V W).subtype} {r : Xo'.XF c' ⟶ Xo.XF c} {ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)}
  {hle : c.F ≤ c'.F} {r₀ : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
  {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} [Fact p.Prime] {Xw : Y.X.Opens} [StarRing (𝓞 E)]




variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  {Y : Model Xo' c' (c'.V W).subtype} {r : Xo'.XF c' ⟶ Xo.XF c} {ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)}
  {hle : c.F ≤ c'.F} {r₀ : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
  {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} [Fact p.Prime] {Xw : Y.X.Opens}




end GlobalTheory.FlatModel

end
