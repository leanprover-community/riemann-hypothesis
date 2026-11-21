import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocPoly
import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.MemIffLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaExponentHnfGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermiteReductionUnipotent
import BuildAid.ForwardExisting
import Formalism.ArtinHasse.ArtinHasseProofs.SymmSeries

section
section
open GroundTheory.Automorphic GLnLocal Iwasawa
open scoped ValuativeRel

namespace GlobalTheory.HermCount

theorem card_res (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (t : ℕ) :
    Nat.card (Res F t) = Spherical.qF F ^ t := by
  have hq := cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal 𝒪[F])
    (IsDiscreteValuationRing.not_a_field _) (i := t)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply, maximalIdeal_pow_eq] at hq
  rw [Res, hq]
  rfl

theorem sum_pos (n : ℕ) (l : Fin n → ℕ) :
    ∑ p : Pos n, l p.1.1 = ∑ i : Fin n, (n - 1 - i.val) * l i := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2)
    (p := fun p : Fin n × Fin n => p.1 < p.2) (by simp) (fun p => l p.1)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter]
  simp only
  rw [Finset.sum_const, smul_eq_mul]
  congr 1
  have : (Finset.univ.filter fun j : Fin n => i < j) = Finset.Ioi i := by
    ext j; simp
  rw [this, Fin.card_Ioi]

theorem card_hData : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) (l : Fin n → ℕ),
    Nat.card (GlobalTheory.HermCount.HData F n l) = Spherical.qF F ^ (∑ i : Fin n, (n - 1 - i.val) * l i) := by
  intro F _ _ _ _ n l
  rw [HData, Nat.card_pi]
  simp only [card_res]
  rw [Finset.prod_pow_eq_pow_sum, sum_pos]

end GlobalTheory.HermCount
end

open GroundTheory.Automorphic GLnLocal Iwasawa
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hermite_data_power_q : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (l : Fin n → ℕ), Nat.card (GlobalTheory.HermCount.HData F n l) = Spherical.qF F ^ (∑ i : Fin n, (n - 1 - i.val) * l i) := by
  atlas_forward_decl GlobalTheory.HermCount.card_hData
end

section
open GroundTheory.Automorphic GLnLocal Iwasawa
open scoped ValuativeRel

namespace GlobalTheory.HermCount
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

instance finite_deg (k : ℕ) : Finite {l : Fin n → ℕ // ∑ i, l i = k} := by
  refine Finite.of_injective (fun l => (⟨l.1, Finset.Nat.mem_antidiagonalTuple.2 l.2⟩ :
    (Finset.Nat.antidiagonalTuple n k : Set (Fin n → ℕ)))) ?_
  intro x y h
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'

instance finite_hdata (l : Fin n → ℕ) : Finite (HData F n l) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [GlobalTheory.T.card_hermite_data_power_q F n l]
  exact pow_ne_zero _ (Spherical.qF_pos (F := F)).ne'

instance finite_hdataDeg (k : ℕ) : Finite (HDataDeg F n k) := inferInstance

end GlobalTheory.HermCount
end

section
noncomputable section

open NumberField IsDedekindDomain Polynomial MeasureTheory GroundTheory.Automorphic UpperTheory.V.Af GlobalTheory.HenQ
open scoped ValuativeRel Pointwise

namespace GlobalTheory.HenQ.ShellOp

section General

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

variable (F n) in

def intShell (k : ℕ) : Set (GL (Fin n) F) :=
  {g | (∀ i j, g.val i j ∈ (ValuativeRel.valuation F).integer) ∧
    ValuativeRel.valuation F g.val.det = ValuativeRel.valuation F (GLnLocal.uniformizer F : F) ^ k}

end General

end GlobalTheory.HenQ.ShellOp

namespace GlobalTheory.HenQ.ShellOp

section Series

end Series

end GlobalTheory.HenQ.ShellOp

namespace GlobalTheory.HenQ.ShellOp

section Hecke

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

theorem esymm_eq (z : Fin n → ℂˣ) (r : ℕ) :
    evalAt z (esymmL n r) = ((Finset.univ.val.map z).map fun b : ℂˣ => (b : ℂ)).esymm r := by
  rw [evalAt_esymmL, Multiset.map_map, Finset.esymm_map_val]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [monomialChar_apply]
  simp only [lamS, Function.comp_apply]
  rw [← Finset.prod_subset (Finset.subset_univ S) (fun i _ hi => by simp [hi])]
  exact Finset.prod_congr rfl fun i hi => by simp [hi]

theorem lamS_univ' : lamS (Finset.univ : Finset (Fin n)) = fun _ => 1 := by
  funext i
  simp [lamS]

theorem gMat_univ' (c : Pairs (Finset.univ : Finset (Fin n)) → 𝓀[F]) :
    gMat Finset.univ c = torusPow F n (fun _ => 1) := by
  have h : unipC (F := F) Finset.univ c = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [coe_unipC, Matrix.add_apply, cMat_apply_of_not c (fun h => h.2.1 (Finset.mem_univ _)), add_zero]
    rfl
  rw [gMat, h, one_mul, lamS_univ']

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem central_mem_of_top (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g)
    (hT : minusculeHecke μ n ∈ eigenSubalgebra μ z f hf) : centralHecke μ ∈ eigenSubalgebra μ z f hf := by
  classical
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  have hp : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    have := Finset.powersetCard_self (Finset.univ : Finset (Fin n))
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have h1 : ∀ g, f (g * torusPow F n (fun _ => 1)) = monomialChar (fun _ : Fin n => 1) z * f g := by
    intro g
    have h := hT g
    haveI : IsEmpty (Pairs (Finset.univ : Finset (Fin n))) := ⟨fun p => p.2.2.1 (Finset.mem_univ _)⟩
    have hc : ∀ I : Fintype (Pairs (Finset.univ : Finset (Fin n)) → 𝓀[F]), (@Finset.univ _ I).card = 1 := by
      intro I
      rw [Subsingleton.elim I Unique.fintype]
      rfl
    rw [integral_minusculeHecke_mul hf, evalAt_satakeTransform_minusculeHecke z le_rfl, evalAt_esymmL, hp,
      Finset.sum_singleton, Finset.sum_singleton, Finset.sum_congr rfl (fun c _ => by rw [gMat_univ' c]),
      Finset.sum_const, hc, one_smul, lamS_univ', Nat.sub_self, mul_zero,
      pow_zero, mul_one, mul_assoc] at h
    exact mul_left_cancel₀ hK h
  have h2 : ∀ g, f (g * torusPow F n (fun _ => -1)) = monomialChar (fun _ : Fin n => -1) z * f g := by
    intro g
    have h := h1 (g * torusPow F n (fun _ => -1))
    have e : (fun _ : Fin n => (-1 : ℤ)) + (fun _ => 1) = 0 := by funext i; simp
    have e' : torusPow F n (fun _ => -1) * torusPow F n (fun _ => 1) = 1 := by
      have : (fun _ : Fin n => (-1 : ℤ)) = -(fun _ => 1) := rfl
      rw [this, torusPow_neg, inv_mul_cancel]
    rw [mul_assoc, e', mul_one] at h
    rw [h, ← mul_assoc, ← monomialChar_add, e, monomialChar_zero, one_mul]
  intro g
  set g₀ := torusPow F n (fun _ : Fin n => (-1 : ℤ))
  have e := integral_mul_left_eq_self (μ := μ)
    (fun x => (centralHecke μ : HeckeAlgebra μ) x * f (g * x)) g₀
  rw [← e]
  have hpt : (fun y => (centralHecke μ : HeckeAlgebra μ) (g₀ * y) *
      f (g * (g₀ * y))) = (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => f (g * g₀)) := by
    funext y
    rw [centralHecke_apply]
    have hiff : g₀ * y ∈ centralSet F n ↔ y ∈ (integralGL F n : Set (GL (Fin n) F)) := by
      rw [mem_centralSet, inv_mul_cancel_left]
      rfl
    by_cases hy : y ∈ (integralGL F n : Set (GL (Fin n) F))
    · rw [Set.indicator_of_mem (hiff.2 hy), Set.indicator_of_mem hy, one_mul, ← mul_assoc, hf _ _ hy]
    · rw [Set.indicator_of_notMem (mt hiff.1 hy), Set.indicator_of_notMem hy, zero_mul]
  rw [hpt, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const,
    Complex.real_smul, h2, satakeTransform_centralHecke, map_smul,
    Spherical.monomial, evalAt_single, one_mul, smul_eq_mul]
  ring

theorem minuscule_mem_of (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) {r : ℕ} (hr : r ≤ n)
    (h : ∀ g, ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
      (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out * f (g * c.out) =
        sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * f g) :
    minusculeHecke μ r ∈ eigenSubalgebra μ z f hf := by
  intro g
  have hcs : HasCompactSupport fun x => (minusculeHecke μ r : HeckeAlgebra μ) x * f (g * x) := by
    refine HasCompactSupport.intro (isCompact_minusculeSet r) fun x hx => ?_
    simp only [minusculeHecke_apply, Set.indicator_of_notMem hx, zero_mul]
  rw [integral_eq_smul_finsum_coset μ (integralOpen F n) (isCompact_integralGL F n) hcs (fun x k hk => by
      rw [(HeckeAlgebraLevel.val_mem _ _ (minusculeHecke μ r) k hk x).2, ← mul_assoc, hf _ k hk]),
    Complex.real_smul, evalAt_satakeTransform_minusculeHecke z hr, mul_assoc, mul_assoc, ← mul_assoc (sqrtQ F ^ _), ← h g]
  rfl

end Hecke

end GlobalTheory.HenQ.ShellOp

namespace GlobalTheory.HenQ.ShellOp

section Global

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra

variable {K : Type} [Field K] [NumberField K]

end Global

end GlobalTheory.HenQ.ShellOp

namespace GlobalTheory.HenQ

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra

end GlobalTheory.HenQ
end
end
