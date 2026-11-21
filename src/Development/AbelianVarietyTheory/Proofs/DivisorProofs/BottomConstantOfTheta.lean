import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantNormalizedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresentaStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairNormPadicValuationBound

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormSum.LemmaC

open GlobalTheory.NormVal

theorem integralOver_cast {D : D7} {p m n : ℕ} (e : n = m) (h : GA D n) (hi : IntegralOver D p h) :
    IntegralOver D p (e ▸ h : GA D m) := by
  subst e; exact hi

theorem exists_cast_eq {D : D7} {p m n : ℕ} (e : n = m) (h' : GA D m) :
    ∃ h : GA D n, (e ▸ h : GA D m) = h' ∧ (IntegralOver D p h' → IntegralOver D p h) := by
  subst e; exact ⟨h', rfl, id⟩

theorem bd_intCast (p : ℕ) [Fact p.Prime] (n : ℤ) : Bd p 1 ((n : ℤ) : ℂ) := by
  have hm : ((n : ℤ) : ℂ) ∈ Qbar := intCast_mem _ n
  refine ⟨hm, fun lam => ?_⟩
  rw [lamC_of_mem lam hm]
  have e1 : (⟨(n : ℂ), hm⟩ : Qbar) = (n : Qbar) := Subtype.ext (by simp)
  rw [e1, map_intCast]
  exact IsUltrametricDist.norm_intCast_le_one _ n

set_option maxHeartbeats 1000000 in

theorem vw_le_of_bottom_pairs : ∀ (D : D7) (N : ℕ) (B : ℝ) (Q : ℕ) (S : Finset ℕ) (del_vp : ℕ → ℝ) (b : ℝ), GlobalTheory.NormSum.Inp D →
    GlobalTheory.NormSum.Exponents S del_vp b → GlobalTheory.NormSum.CoordInt D N B Q del_vp →
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (w : Formalism.PairingDivisionLocalBalance.Pl K) (p : ℕ) [Fact p.Prime],
    (p : 𝓞 K) ∈ w.asIdeal → ∀ (δ t0 : ℂ) (Q₁ Q₂ : ℕ), padicValNat p Q₁ ≤ padicValNat p Q →
    padicValNat p Q₂ ≤ padicValNat p Q →
    ∀ (P₁ P₁' : Pair D ⊤ δ t0 Q₁) (P₂ P₂' : Pair D ⊤ δ t0 Q₂), P₁.Small N B → P₁'.Small N B → P₂.Small N B →
    P₂'.Small N B → ∀ (hd₁ : P₁'.d = P₁.d) (hd₂ : P₂'.d = P₂.d) (b₁ b₂ v : ℂ)
    (M₁ : Tup D P₁.a P₁.d P₁.n → Tup D P₁'.a P₁'.d P₁'.n → ℤ) (M₂ : Tup D P₂'.a P₂'.d P₂'.n → Tup D P₂.a P₂.d P₂.n → ℤ),
    (∀ (h : GA D P₁.d) T, starRingEnd ℂ (P₁.coord h T) = b₁ * ∑ T', (M₁ T T' : ℂ) * P₁'.coord (hd₁ ▸ h) T') →
    (∀ (h : GA D P₂.d) T', P₂'.coord (hd₂ ▸ h) T' * b₂ = ∑ T, (M₂ T' T : ℂ) * starRingEnd ℂ (P₂.coord h T)) →
    b₂ ≠ 0 → v ∈ Qbar → (∀ lam : Qbar →+* ℂ_[p], ‖lamC lam v‖ = 1) →
    ∀ (γ z z' : K), b₁ = σ γ * b₂ * v → σ z = (P₁.norm : ℂ) → σ z' = (P₂'.norm : ℂ) → z ≠ 0 → z' ≠ 0 →
    (vw w γ : ℝ) ≤ vw w z + vw w z' + 6 * Formalism.PairingDivisionLocalBalance.wt S del_vp w := by
  intro D N B Q S del_vp b hI hE hC K _ _ _ σ w p _ hw δ t0 Q₁ Q₂ hQ₁ hQ₂ P₁ P₁' P₂ P₂' hs₁ hs₁' hs₂ hs₂' hd₁ hd₂ b₁ b₂ v M₁ M₂ hr₁ hr₂ hb₂ hv hv1 γ z z' hγ hz hz' hz0 hz0'
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp0 : (0 : ℝ) < p := by linarith
  set e : ℝ := del_vp p with he
  set r : ℝ := (p : ℝ) ^ e with hr
  have hr0 : 0 ≤ r := by positivity

  have hgam : ∀ {Q' : ℕ} (P : Pair D ⊤ δ t0 Q'), padicValNat p Q' ≤ padicValNat p Q → P.Small N B →
      ∀ g, Bd p r ((gam D P.J g : ℂ)⁻¹) := fun P hQ' hS g => by
    obtain ⟨-, h2, -⟩ := hC δ t0 p _ hQ' P hS
    exact (Bd.inv_nat (h2 g).1 dvd_rfl).mono (Real.rpow_le_rpow_of_exponent_le hp1 (h2 g).2)

  have hco : ∀ {Q' : ℕ} (P : Pair D ⊤ δ t0 Q'), padicValNat p Q' ≤ padicValNat p Q → P.Small N B →
      ∀ g, IntegralOver D p g → ∀ T, Bd p r (P.coord g T) := fun P hQ' hS g hg T =>
    (hC δ t0 p _ hQ' P hS).2.2 g hg T

  have hb₁ : b₁ ≠ 0 := by
    rintro rfl
    have h0 : P₁.norm = 0 := by
      unfold Pair.norm
      refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
      have : P₁.sq q.out = 0 := by
        unfold Pair.sq
        refine Finset.sum_eq_zero fun T _ => ?_
        have := hr₁ q.out T
        rw [zero_mul, map_eq_zero] at this
        rw [this, norm_zero]; norm_num
      rw [this, mul_zero]
    apply hz0
    apply σ.injective
    rw [hz, h0, map_zero, Complex.ofReal_zero]
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul, zero_mul] at hγ
    exact hb₁ hγ
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hγ
    exact hb₁ hγ

  have hA : Bd p (r * (r * (1 * r))) ((P₁.norm : ℂ) * b₁⁻¹) := by
    obtain ⟨h1, -, -⟩ := hC δ t0 p Q₁ hQ₁ P₁ hs₁
    choose s hs1 hs2 using h1
    rw [(GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives D hI ⊤ δ t0 Q₁ P₁.crv P₁.pt0 P₁ P₁.level_pos).2.2.2.1 s hs1]
    refine finsum_induction (fun x : ℝ => Bd p (r * (r * (1 * r))) ((x : ℂ) * b₁⁻¹)) ?_
      (fun x y hx hy => ?_) (fun q => ?_)
    · beta_reduce; rw [Complex.ofReal_zero, zero_mul]; exact Bd.zero (by positivity)
    · beta_reduce at hx hy ⊢; rw [Complex.ofReal_add, add_mul]; exact hx.add hy
    · beta_reduce; rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, mul_assoc]
      refine Bd.mul (hgam P₁ hQ₁ hs₁ _) ?_
      unfold Pair.sq
      rw [Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T _ => ?_)
      have e1 : ((‖P₁.coord (s q) T‖ ^ 2 : ℝ) : ℂ) * b₁⁻¹ =
          P₁.coord (s q) T * ∑ T', (M₁ T T' : ℂ) * P₁'.coord (hd₁.symm ▸ s q) T' := by
        rw [Complex.ofReal_pow, ← Complex.mul_conj', hr₁]
        field_simp
      rw [e1]
      refine (hco P₁ hQ₁ hs₁ _ (hs2 q) T).mul ?_
      refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T' _ => ?_)
      exact (bd_intCast p _).mul (hco P₁' hQ₁ hs₁' _ (integralOver_cast hd₁.symm _ (hs2 q)) T')

  have hB : Bd p (r * (r * (1 * r))) ((P₂'.norm : ℂ) * b₂) := by
    obtain ⟨h1, -, -⟩ := hC δ t0 p Q₂ hQ₂ P₂' hs₂'
    choose s hs1 hs2 using h1
    rw [(GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives D hI ⊤ δ t0 Q₂ P₂'.crv P₂'.pt0 P₂' P₂'.level_pos).2.2.2.1 s hs1]
    refine finsum_induction (fun x : ℝ => Bd p (r * (r * (1 * r))) ((x : ℂ) * b₂)) ?_
      (fun x y hx hy => ?_) (fun q => ?_)
    · beta_reduce; rw [Complex.ofReal_zero, zero_mul]; exact Bd.zero (by positivity)
    · beta_reduce at hx hy ⊢; rw [Complex.ofReal_add, add_mul]; exact hx.add hy
    · beta_reduce; rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, mul_assoc]
      refine Bd.mul (hgam P₂' hQ₂ hs₂' _) ?_
      unfold Pair.sq
      rw [Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T' _ => ?_)
      obtain ⟨h, hh, hi⟩ := exists_cast_eq (p := p) hd₂.symm (s q)
      have e1 : ((‖P₂'.coord (s q) T'‖ ^ 2 : ℝ) : ℂ) * b₂ =
          (starRingEnd ℂ) (P₂'.coord (s q) T') * ∑ T, (M₂ T' T : ℂ) * (starRingEnd ℂ) (P₂.coord h T) := by
        rw [← hr₂ h T', hh, Complex.ofReal_pow, ← Complex.mul_conj']
        ring
      rw [e1]
      refine (hco P₂' hQ₂ hs₂' _ (hs2 q) T').conj.mul ?_
      refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T _ => ?_)
      exact (bd_intCast p _).mul (hco P₂ hQ₂ hs₂ _ (hi (hs2 q)) T).conj

  set x : K := z * z' * γ⁻¹ with hx
  have hx0 : x ≠ 0 := mul_ne_zero (mul_ne_zero hz0 hz0') (inv_ne_zero hγ0)
  have hσx : σ x = ((P₁.norm : ℂ) * b₁⁻¹) * ((P₂'.norm : ℂ) * b₂) * v := by
    have hσγ : σ γ ≠ 0 := (map_ne_zero σ).2 hγ0
    rw [hx, map_mul, map_mul, map_inv₀, hz, hz', hγ]
    field_simp
  have hX : Bd p (r * (r * (1 * r)) * (r * (r * (1 * r))) * 1) (σ x) := by
    rw [hσx]
    exact (hA.mul hB).mul ⟨hv, fun lam => (hv1 lam).le⟩
  have hpow : r * (r * (1 * r)) * (r * (r * (1 * r))) * 1 = (p : ℝ) ^ (6 * e) := by
    rw [mul_comm 6 e, Real.rpow_mul hp0.le, hr]
    norm_num
    ring
  have key := GlobalTheory.PadicPlaceBound.neg_mul_vw_le_vw K σ x p w (6 * e) hx0 hw fun lam =>
    (hX.2 lam).trans (le_of_eq hpow)
  have hvx : (Formalism.DivisionValues.vw w x : ℝ) = Formalism.DivisionValues.vw w z + Formalism.DivisionValues.vw w z' - Formalism.DivisionValues.vw w γ := by
    rw [hx, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (mul_ne_zero hz0 hz0') (inv_ne_zero hγ0),
      Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hz0 hz0', Formalism.DivisionValues.ValuationRepresentative.vw_inv]
    push_cast; ring
  rw [hE.wt_eq hp w hw]
  rw [hvx] at key
  linarith

end GlobalTheory.NormSum.LemmaC
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_proportionalityRatio_le_bottomPairs : ∀ (D : D7) (N : ℕ) (B : ℝ) (Q : ℕ) (S : Finset ℕ) (del_vp : ℕ → ℝ) (b : ℝ), GlobalTheory.NormSum.Inp D →
    GlobalTheory.NormSum.Exponents S del_vp b → GlobalTheory.NormSum.CoordInt D N B Q del_vp →
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (w : Formalism.PairingDivisionLocalBalance.Pl K) (p : ℕ) [Fact p.Prime],
    (p : 𝓞 K) ∈ w.asIdeal → ∀ (δ t0 : ℂ) (Q₁ Q₂ : ℕ), padicValNat p Q₁ ≤ padicValNat p Q →
    padicValNat p Q₂ ≤ padicValNat p Q →
    ∀ (P₁ P₁' : Pair D ⊤ δ t0 Q₁) (P₂ P₂' : Pair D ⊤ δ t0 Q₂), P₁.Small N B → P₁'.Small N B → P₂.Small N B →
    P₂'.Small N B → ∀ (hd₁ : P₁'.d = P₁.d) (hd₂ : P₂'.d = P₂.d) (b₁ b₂ v : ℂ)
    (M₁ : Tup D P₁.a P₁.d P₁.n → Tup D P₁'.a P₁'.d P₁'.n → ℤ) (M₂ : Tup D P₂'.a P₂'.d P₂'.n → Tup D P₂.a P₂.d P₂.n → ℤ),
    (∀ (h : GA D P₁.d) T, starRingEnd ℂ (P₁.coord h T) = b₁ * ∑ T', (M₁ T T' : ℂ) * P₁'.coord (hd₁ ▸ h) T') →
    (∀ (h : GA D P₂.d) T', P₂'.coord (hd₂ ▸ h) T' * b₂ = ∑ T, (M₂ T' T : ℂ) * starRingEnd ℂ (P₂.coord h T)) →
    b₂ ≠ 0 → v ∈ Qbar → (∀ lam : Qbar →+* ℂ_[p], ‖lamC lam v‖ = 1) →
    ∀ (γ z z' : K), b₁ = σ γ * b₂ * v → σ z = (P₁.norm : ℂ) → σ z' = (P₂'.norm : ℂ) → z ≠ 0 → z' ≠ 0 →
    (vw w γ : ℝ) ≤ vw w z + vw w z' + 6 * Formalism.PairingDivisionLocalBalance.wt S del_vp w := by
  atlas_forward_decl GlobalTheory.NormSum.LemmaC.vw_le_of_bottom_pairs
end

section
namespace GlobalTheory.PrimeMembershipExistence

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) :
    ∃ p : ℕ, Nat.Prime p ∧
      (p : NumberField.RingOfIntegers K) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal w := by

  have hP := w.isPrime
  have hn0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hmem := Ideal.absNorm_mem w.asIdeal
  rw [← Nat.prod_factorization_pow_eq_self hn0, Finsupp.prod, Nat.cast_prod] at hmem
  obtain ⟨p, hp, hpm⟩ := hP.prod_mem_iff.1 hmem
  rw [Nat.support_factorization] at hp
  rw [Nat.cast_pow] at hpm
  exact ⟨p, Nat.prime_of_mem_primeFactors hp, hP.mem_of_pow_mem _ hpm⟩

end GlobalTheory.PrimeMembershipExistence
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTop.BotConstPf

theorem gBig_imp {P R : GP} (hP : GBig P)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → R G μ₀ C x b) : GBig R := by
  obtain ⟨CF0, h1⟩ := hP
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h2⟩ := h1 ε CF hCF
  exact ⟨C0, x0, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ (h2 C hC D large₂ he hx hr T Lc μ₀ hμ G)⟩

theorem exists_prime_under {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ w.asIdeal := by
  first
  | exact @_root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem
  | exact _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem
  | (apply _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem ..)

theorem lamC_div_norm {p : ℕ} [Fact p.Prime] {u₁ u₂ : ℂ} (h₁ : u₁ ∈ Qbar) (h₂ : u₂ ∈ Qbar)
    (n₁ : ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u₁‖ = 1) (n₂ : ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u₂‖ = 1) :
    u₁ / u₂ ∈ Qbar ∧ ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam (u₁ / u₂)‖ = 1 := by
  have h3 : u₁ / u₂ ∈ Qbar := div_mem h₁ h₂
  refine ⟨h3, fun lam => ?_⟩
  have e : (⟨u₁ / u₂, h3⟩ : Qbar) = ⟨u₁, h₁⟩ / ⟨u₂, h₂⟩ := rfl
  have a := n₁ lam
  have b := n₂ lam
  rw [lamC, dif_pos h₁] at a
  rw [lamC, dif_pos h₂] at b
  rw [lamC, dif_pos h3, e, map_div₀, norm_div, a, b, div_one]

end GlobalTheory.SqTop.BotConstPf

namespace GlobalTheory.SqTop

open BotConstPf

theorem botConst_of_inputs : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → BotSmall → LNe → BotConst := by
  intro hPr hK hM hInp hS hL
  refine gBig_imp (Model.gBig_and (Model.gBig_and (GlobalTheory.T.bottom_triangle_constant_at hPr hK hM hInp hS hL) (GlobalTheory.T.bottom_triangle_constant_normalized hPr hK hM hInp hS)) hS) ?_
  intro D T Lc sc G μ₀ C x b hμ H
  obtain ⟨⟨H1, H2⟩, hGood, htw, hSm⟩ := H
  intro W S hψ hN i j t A A' WW X c0 δ t0 P₀ P₀' P P' z z' C' dl hX hc hB₀ hB hz hz' hz0 hz'0 hI
  obtain ⟨hct, hc0, γ, hγ⟩ := H1 W S hψ hN i j t A A' WW X c0 hX hc
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hγ
    exact hct hγ.symm
  refine ⟨γ, hγ0, hc0, hγ, fun w hw => ?_⟩
  obtain ⟨κ, hκ, H⟩ := H2 W S hψ hN i j A A' WW X c0 δ t0 hX hc
  obtain ⟨-, hQn1, hmod⟩ := Model.base_tuple G hμ
  obtain ⟨u₁, M, M', hu₁, hu₁q, hu₁n, hr₁⟩ := H t _ P P' hB
  obtain ⟨u₂, N₁, N₂, hu₂, hu₂q, hu₂n, hr₂⟩ := H μ₀ _ P₀ P₀' (hmod ▸ hB₀)
  obtain ⟨S', del, hE, hCo, -, rfl⟩ := hI
  obtain ⟨p, hp, hpw⟩ := exists_prime_under w
  haveI : Fact p.Prime := ⟨hp⟩
  have hpQ : ¬ p ∣ Qn G t := fun hd => hw (by
    obtain ⟨k, hk⟩ := hd
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hpw)
  have hp1 : ¬ p ∣ Qn G μ₀ := by rw [hQn1]; exact hp.not_dvd_one
  obtain ⟨hv, hvn⟩ := lamC_div_norm hu₁q hu₂q (hu₁n p hpQ) (hu₂n p hp1)
  have hlev : padicValNat p (levQ G.pl * Qn G t) ≤ padicValNat p (levQ G.pl) := by
    have h0 : levQ G.pl ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ =>
      pow_ne_zero _ (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
    rw [padicValNat.mul h0 (Model.Qn_ne_zero G t), padicValNat.eq_zero_of_not_dvd hpQ, add_zero]
  have e1 := hB.rank
  have e2 := hB₀.rank
  have s1 := hSm δ t0 _ P P' t i j _ hB
  have s2 := hSm δ t0 _ P₀ P₀' μ₀ i j _ hB₀
  refine GlobalTheory.T.valuation_proportionalityRatio_le_bottomPairs D (bigN D) (maxWt D sc.cGap) (levQ G.pl) S' del _ (hInp D) hE hCo D.what₂.LL D.what₂.embLL w p hpw δ t0
    (levQ G.pl * Qn G t) (levQ G.pl) hlev le_rfl P P' P₀ P₀' s1.1 s1.2 s2.1 s2.2 e1.2.2.2 e2.2.2.2
    (κ * u₁ * c0 t) (κ * u₂ * c0 μ₀) (u₁ / u₂) M N₂ (fun h T => (hr₁ e1.2.2.2 h).1 T)
    (fun h T' => (hr₂ e2.2.2.2 h).2 T') (mul_ne_zero (mul_ne_zero hκ hu₂) hc0) hv hvn γ z z' ?_ hz hz' hz0 hz'0
  rw [← hγ]
  field_simp

end GlobalTheory.SqTop

end
end
