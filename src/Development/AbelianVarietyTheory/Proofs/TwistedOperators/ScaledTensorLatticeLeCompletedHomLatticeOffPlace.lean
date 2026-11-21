import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatOEqHatA
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjIdempotentConjFixed
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import BuildAid.ForwardExisting

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemSumFinAdele

theorem exists_finAdele_of_idemSum : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∃ σ : Af D.host.F, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) = e + cA D e ∧ (∀ w : HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ P, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → evalV D.host.F w σ = 0) ∧ ∀ PP ∈ P, evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) σ = 1 := by
  intro D P e he
  have he' := he
  obtain ⟨⟨es, hes, rfl⟩, hz⟩ := he
  have hex : ∀ PP ∈ P, ∃ α : Af D.host.F,
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = es PP + cA D (es PP) ∧
      evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) α = 1 ∧
      ∀ v', v' ≠ HeightOneSpectrum.under (𝓞 D.host.F) PP → evalV D.host.F v' α = 0 := by
    intro PP hPP
    obtain ⟨⟨a1, a2, v, ε, hε, a3⟩, -⟩ := hes PP hPP
    have hv := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP v ε (hes PP hPP) hε a3
    obtain ⟨α, rfl, h1, h2⟩ := hε
    exact ⟨α, a3.symm, hv ▸ h1, hv ▸ h2⟩
  choose! α hα using hex
  have hsum : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (∑ PP ∈ P, α PP)) =
      ∑ PP ∈ P, es PP + cA D (∑ PP ∈ P, es PP) := by
    have hp : pairA D.host.F 0 (∑ PP ∈ P, α PP) = ∑ PP ∈ P, pairA D.host.F 0 (α PP) := by
      have hadd : ∀ a b : Af D.host.F, pairA D.host.F 0 (a + b) = pairA D.host.F 0 a + pairA D.host.F 0 b :=
        fun a b => Prod.ext (add_zero 0).symm rfl
      exact map_sum (AddMonoidHom.mk' (pairA D.host.F 0) hadd) α P
    rw [hp, map_sum, map_sum (cA D), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun PP hPP => (hα PP hPP).1
  refine ⟨∑ PP ∈ P, α PP, hsum, ?_, ?_⟩
  · intro w hw
    rw [map_sum]
    exact Finset.sum_eq_zero fun PP hPP => (hα PP hPP).2.2 w (hw PP hPP).symm
  · intro PP hPP
    have h1 := GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one P _ he' PP hPP
    rw [← hsum] at h1
    have h2 : (evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) (∑ PP ∈ P, α PP)) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (1 : Fv D.host.F _ ⊗[D.host.F] D.host.E) := h1
    haveI : Module.Free D.host.F (Fv D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP)) :=
      Module.Free.of_divisionRing _ _
    haveI : Module.Flat D.host.F (Fv D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP)) := Module.Flat.of_free
    have hinj := Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F)
      (A := Fv D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP)) (B := D.host.E) (algebraMap D.host.F D.host.E).injective
    apply hinj
    rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeLeft_apply, h2]
    rfl

end GlobalTheory.IdemSumFinAdele

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdele_of_splitPlaces_idempotentSum : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∃ σ : Af D.host.F, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) = e + cA D e ∧ (∀ w : HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ P, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → evalV D.host.F w σ = 0) ∧ ∀ PP ∈ P, evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) σ = 1 := by
  first | exact @GlobalTheory.IdemSumFinAdele.exists_finAdele_of_idemSum | exact GlobalTheory.IdemSumFinAdele.exists_finAdele_of_idemSum | (intros; apply GlobalTheory.IdemSumFinAdele.exists_finAdele_of_idemSum <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HatPoint

section Gen

variable {F : Type} [Field F] [NumberField F]

theorem ev_apply (v : HeightOneSpectrum (𝓞 F)) (x : Af F) : evalV F v x = x v := rfl

theorem val_coe_one (t : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (ht : t ∉ v.asIdeal) :
    Valued.v (algebraMap F (Af F) (t : F) v) = 1 := by
  rw [GlobalTheory.Ker.MovLev.val_coe]; exact v.intValuation_eq_one_iff.2 ht

theorem coe_ne_zero (t : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (ht : t ∉ v.asIdeal) :
    algebraMap F (Af F) (t : F) v ≠ 0 := fun h0 => by
  have := val_coe_one t v ht
  rw [h0, map_zero] at this
  exact zero_ne_one this

theorem div_int {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F} (hx : x ∈ v.adicCompletionIntegers F)
    (t : 𝓞 F) (ht : t ∉ v.asIdeal) : x * (algebraMap F (Af F) (t : F) v)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
  rw [map_mul, map_inv₀, val_coe_one t v ht, inv_one, mul_one]
  exact hx

def mulG (I : Ideal (𝓞 F)) : AddSubgroup (Af F) :=
  AddSubgroup.closure {x | ∃ t ∈ I, ∃ β ∈ intAf F, x = algebraMap F (Af F) (t : F) * β}

theorem mem_mulG (I : Ideal (𝓞 F)) {γ : Af F} (hγ : γ ∈ intAf F)
    (h : ∀ w : HeightOneSpectrum (𝓞 F), evalV F w γ = 0 ∨ ∃ t ∈ I, t ∉ w.asIdeal) : γ ∈ mulG I := by
  by_cases h0 : γ = 0
  · rw [h0]; exact zero_mem _
  obtain ⟨w₀, hw₀⟩ : ∃ w, γ w ≠ 0 := by
    by_contra H
    push_neg at H
    exact h0 (FiniteAdeleRing.ext F fun v => H v)
  obtain ⟨t₁, ht₁I, ht₁w⟩ := (h w₀).resolve_left hw₀
  have ht₁0 : t₁ ≠ 0 := fun e => ht₁w (e ▸ w₀.asIdeal.zero_mem)
  have hspan : Ideal.span {t₁} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ht₁0
  set Z := (Ideal.finite_factors hspan).toFinset with hZdef
  have hZ : ∀ v, v ∈ Z ↔ t₁ ∈ v.asIdeal := fun v => by
    rw [hZdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  have h' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t ∈ I, γ v = 0 ∨ t ∉ v.asIdeal := fun v =>
    (h v).elim (fun e => ⟨0, I.zero_mem, Or.inl e⟩) fun ⟨t, ht, hv⟩ => ⟨t, ht, Or.inr hv⟩
  choose τ hτI hτ using h'
  obtain ⟨c, hc, hc'⟩ : ∃ c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F,
      (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ ∀ v, algebraMap F (Af F) (τ v : F) v * c v = γ v := by
    refine ⟨fun v => if γ v = 0 then 0 else γ v * (algebraMap F (Af F) (τ v : F) v)⁻¹, fun v => ?_, fun v => ?_⟩
    · dsimp only
      split_ifs with hv
      · exact zero_mem _
      · exact div_int (hγ v) _ ((hτ v).resolve_left hv)
    · dsimp only
      split_ifs with hv
      · rw [mul_zero, hv]
      · rw [mul_comm, mul_assoc, inv_mul_cancel₀ (coe_ne_zero _ _ ((hτ v).resolve_left hv)), mul_one]
  have hb₁ : ∀ v : HeightOneSpectrum (𝓞 F),
      (if t₁ ∈ v.asIdeal then 0 else γ v * (algebraMap F (Af F) (t₁ : F) v)⁻¹) ∈ v.adicCompletionIntegers F :=
    fun v => by
      split_ifs with hv
      · exact zero_mem _
      · exact div_int (hγ v) _ hv
  obtain ⟨β₁, hβ₁, eβ₁⟩ : ∃ β₁ : Af F, β₁ ∈ intAf F ∧
      ∀ v, β₁ v = if t₁ ∈ v.asIdeal then 0 else γ v * (algebraMap F (Af F) (t₁ : F) v)⁻¹ :=
    ⟨GlobalTheory.Ker.MovLev.ofInt _ hb₁, fun v => hb₁ v, fun _ => rfl⟩
  have hbw : ∀ w v : HeightOneSpectrum (𝓞 F), (if v = w then c v else 0) ∈ v.adicCompletionIntegers F :=
    fun w v => by
      split_ifs
      exacts [hc v, zero_mem _]
  have hβex : ∀ w : HeightOneSpectrum (𝓞 F), ∃ β : Af F, β ∈ intAf F ∧ ∀ v, β v = if v = w then c v else 0 :=
    fun w => ⟨GlobalTheory.Ker.MovLev.ofInt _ (hbw w), fun v => hbw w v, fun _ => rfl⟩
  choose β hβ eβ using hβex
  have e : γ = algebraMap F (Af F) (t₁ : F) * β₁ + ∑ w ∈ Z, algebraMap F (Af F) (τ w : F) * β w := by
    refine FiniteAdeleRing.ext F fun v => ?_
    change evalV F v γ = evalV F v (algebraMap F (Af F) (t₁ : F) * β₁ + ∑ w ∈ Z, algebraMap F (Af F) (τ w : F) * β w)
    rw [map_add, map_sum, map_mul]
    simp only [map_mul, ev_apply, eβ₁, eβ]
    by_cases hv : t₁ ∈ v.asIdeal
    · have hvZ : v ∈ Z := (hZ v).2 hv
      rw [Finset.sum_eq_single v (fun w _ hwv => by rw [if_neg (Ne.symm hwv), mul_zero])
        (fun hn => absurd hvZ hn), if_pos hv, if_pos rfl, mul_zero, zero_add, hc']
    · rw [Finset.sum_eq_zero (fun w hw => by
        have hne : v ≠ w := fun e => hv (e ▸ (hZ w).1 hw)
        rw [if_neg hne, mul_zero]), if_neg hv, add_zero, mul_comm, mul_assoc,
        inv_mul_cancel₀ (coe_ne_zero _ _ hv), mul_one]
  rw [e]
  refine add_mem (AddSubgroup.subset_closure ⟨t₁, ht₁I, β₁, hβ₁, rfl⟩) (sum_mem fun w _ => ?_)
  exact AddSubgroup.subset_closure ⟨τ w, hτI w, β w, hβ w, rfl⟩

theorem pairA_mul_tmul {E : Type} [Field E] [Algebra F E] (s : F) (β : Af F) (x : E) :
    pairA F 0 (algebraMap F (Af F) s * β) ⊗ₜ[F] x = pairA F 0 β ⊗ₜ[F] (algebraMap F E s * x) := by
  have h : pairA F 0 (algebraMap F (Af F) s * β) = s • pairA F 0 β :=
    Prod.ext (by change (0 : Ainf F) = s • 0; rw [smul_zero]) (by change _ = s • β; rw [Algebra.smul_def]; rfl)
  rw [h, TensorProduct.smul_tmul, Algebra.smul_def]

end Gen

theorem mem_hatA_of_div : ∀ (D : D7) (S T : HSp D) (A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)), (∀ (c : 𝓞 D.host.F), ∀ y ∈ A, (algebraMap D.host.F D.host.E (c : D.host.F)) • y ∈ A) → ∀ γ ∈ intAf D.host.F, ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, (∀ w : HeightOneSpectrum (𝓞 D.host.F), evalV D.host.F w γ = 0 ∨ ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ (algebraMap D.host.F D.host.E (t : D.host.F)) • y ∈ A) → (Matrix.of fun a k => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] y k a : WO S T) ∈ hatA S T A := by
  intro D S T A hA γ hγ y hy
  let I : Ideal (𝓞 D.host.F) :=
    { carrier := {t | algebraMap D.host.F D.host.E (t : D.host.F) • y ∈ A}
      add_mem' := fun {a b} ha hb => by
        change algebraMap D.host.F D.host.E ((a : D.host.F) + (b : D.host.F)) • y ∈ A
        rw [map_add, add_smul]
        exact add_mem ha hb
      zero_mem' := by
        change algebraMap D.host.F D.host.E (0 : D.host.F) • y ∈ A
        rw [map_zero, zero_smul]
        exact zero_mem _
      smul_mem' := fun c {x} hx => by
        change algebraMap D.host.F D.host.E ((c : D.host.F) * (x : D.host.F)) • y ∈ A
        rw [map_mul, mul_smul]
        exact hA c _ hx }
  have hmem := mem_mulG I hγ fun w => (hy w).imp id fun ⟨t, ht, hA'⟩ => ⟨t, hA', ht⟩
  let f : Af D.host.F →+ WO S T :=
    { toFun := fun α => Matrix.of fun a k => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a
      map_zero' := Matrix.ext fun a k => by
        change pairA D.host.F 0 0 ⊗ₜ[D.host.F] y k a = 0
        exact TensorProduct.zero_tmul _ _
      map_add' := fun α β => Matrix.ext fun a k => by
        change pairA D.host.F 0 (α + β) ⊗ₜ[D.host.F] y k a =
          pairA D.host.F 0 α ⊗ₜ[D.host.F] y k a + pairA D.host.F 0 β ⊗ₜ[D.host.F] y k a
        rw [← TensorProduct.add_tmul]
        congr 1
        exact Prod.ext (add_zero 0).symm rfl }
  have hle : mulG I ≤ (hatA S T A).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨t, ht, β, hβ, rfl⟩
    refine AddSubgroup.subset_closure ⟨β, hβ, _, ht, ?_⟩
    refine Matrix.ext fun a k => ?_
    change pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (t : D.host.F) * β) ⊗ₜ[D.host.F] y k a =
      pairA D.host.F 0 β ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (t : D.host.F) • y) k a
    rw [pairA_mul_tmul, Matrix.smul_apply, smul_eq_mul]
  exact hle hmem

end GlobalTheory.HatPoint

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedMatrixGroup_of_local_multiplier : ∀ (D : D7) (S T : HSp D) (A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)), (∀ (c : 𝓞 D.host.F), ∀ y ∈ A, (algebraMap D.host.F D.host.E (c : D.host.F)) • y ∈ A) → ∀ γ ∈ intAf D.host.F, ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, (∀ w : HeightOneSpectrum (𝓞 D.host.F), evalV D.host.F w γ = 0 ∨ ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ (algebraMap D.host.F D.host.E (t : D.host.F)) • y ∈ A) → (Matrix.of fun a k => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] y k a : WO S T) ∈ hatA S T A := by
  first | exact @GlobalTheory.HatPoint.mem_hatA_of_div | exact GlobalTheory.HatPoint.mem_hatA_of_div | (intros; apply GlobalTheory.HatPoint.mem_hatA_of_div <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.MoverStd

theorem exists_mul_std : ∀ (D : D7) (S : HSp D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank) (σ : Af D.host.F) (w : HeightOneSpectrum (𝓞 D.host.F)), evalV D.host.F w σ = 0 → (∀ i j, (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)) * (mt S k₀⁻¹ - 1) i j = 0) → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ v ∈ Λ', ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • v ∈ stdL D.host.E S.rank := by
  intro D S k₀ Λ' σ w hσ hk hm v hv
  obtain ⟨hfg, -, -⟩ := Base.stdL_mem_Vset (E := D.host.E) S.rank 1
  have hs : Submodule.span D.host.E (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) = ⊤ := by
    rw [stdL, Submodule.span_span_of_tower, ← (Pi.basisFun D.host.E (Fin S.rank)).span_eq]
    congr 2
    funext i
    simp
  have ht : ∀ u, MovLev.lf (MovLev.idem w.asIdeal) • (fmtC S k₀⁻¹ *ᵥ u) = MovLev.lf (MovLev.idem w.asIdeal) • u :=
    fun u => MovLev.smul_mulVec_eq _ _ (fun v' => by
      by_cases hv' : w.asIdeal ≤ v'.asIdeal
      · have e : v' = w := (HeightOneSpectrum.ext (w.isMaximal.eq_of_le v'.isPrime.ne_top hv')).symm
        subst e
        refine Or.inr fun ε hε i j => ?_
        obtain ⟨α, rfl, -, hα0⟩ := hε
        have hασ : α * σ = 0 := by
          refine FiniteAdeleRing.ext D.host.F fun u => ?_
          change α u * σ u = 0
          by_cases hu : u = v'
          · subst hu
            rw [show σ u = 0 from hσ, mul_zero]
          · rw [show α u = 0 from hα0 u hu, zero_mul]
        have hmul : pairA D.host.F 0 α * (1 - pairA D.host.F 0 σ) = pairA D.host.F 0 α := by
          refine Prod.ext ?_ ?_
          · change (0 : Ainf D.host.F) * (1 - 0) = 0
            rw [zero_mul]
          · change α * (1 - σ) = α
            rw [mul_sub, mul_one, hασ, sub_zero]
        have h0 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * (mt S k₀⁻¹ - 1) i j = 0 := by
          rw [← hmul, map_mul, mul_assoc, map_sub, map_one, hk i j, mul_zero]
        have := congrArg (cA D) h0
        rw [map_mul, map_zero, Matrix.sub_apply, map_sub] at this
        have e1 : cA D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) =
            algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) := by
          change (pairA D.host.F 0 α) ⊗ₜ D.sp.cm.sig 1 = (pairA D.host.F 0 α) ⊗ₜ 1
          rw [map_one]
        have e' : cA D ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
            (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by
          rw [Matrix.one_apply]
          split_ifs
          exacts [map_one _, map_zero _]
        rw [e1, e'] at this
        exact this
      · exact Or.inl (if_neg hv')) u
  obtain ⟨t, htw, H⟩ := MovLev.exists_mul (E := D.host.E) w.asIdeal.primeCompl w.asIdeal (fun v' hv' => by
      have h1 : ¬ v'.asIdeal ≤ w.asIdeal := fun h => hv' ((v'.isMaximal.eq_of_le w.isPrime.ne_top h) ▸ le_rfl)
      obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 h1
      exact ⟨a, ha', ha⟩)
    (L := Submodule.span (𝓞 D.host.E) {v}) (Λ := stdL D.host.E S.rank) (Submodule.fg_span_singleton v) hfg hs
    (fun z hz => by
      have hz' : z ∈ GlobalTheory.AdLat.hat D.host.F (Λ' : Set (Fin S.rank → D.host.E)) := AddSubgroup.closure_mono (by
        rintro y ⟨a, ha, x, hx, e⟩
        exact ⟨a, ha, x, (Submodule.span_le.2 (Set.singleton_subset_iff.2 hv)) hx, e⟩) hz
      change MovLev.lf (MovLev.idem w.asIdeal) • z ∈ _
      rw [← ht z]
      exact MovLev.hat_int (MovLev.idem_int _) ((hm _).2 ⟨z, hz', rfl⟩))
  exact ⟨t, htw, H v (Submodule.mem_span_singleton_self v)⟩

end GlobalTheory.Ker.MoverStd
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiplier_standard_lattice_of_mover_trivial : ∀ (D : D7) (S : HSp D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank) (σ : Af D.host.F) (w : HeightOneSpectrum (𝓞 D.host.F)), evalV D.host.F w σ = 0 → (∀ i j, (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)) * (mt S k₀⁻¹ - 1) i j = 0) → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ v ∈ Λ', ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • v ∈ stdL D.host.E S.rank := by
  atlas_forward_decl GlobalTheory.Ker.MoverStd.exists_mul_std
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TrOffShift

theorem algebraMap_mem_conjI {D : D7} (I : Ideal (𝓞 D.host.E)) (s : 𝓞 D.host.F)
    (h : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ I) :
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ conjI I := by
  apply Ideal.subset_span
  refine ⟨_, h, ?_⟩
  have h2 := GlobalTheory.Ker.MovLev.bar_algebraMap (D := D) s
  have h3 := congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) h2
  simp only [Lev.bar] at h3
  have h4 := IsCMField.coe_ringOfIntegersComplexConj D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s)
  exact h3.symm.trans h4

theorem shift_mult : ∀ (D : D7) (r : ℕ) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (L : Lt D.host.E r) (w : HeightOneSpectrum (𝓞 D.host.F)), (∀ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → ∀ u ∈ idq (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) L, ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • u ∈ L := by
  intro D r Pg Q L w hne u hu
  classical
  have hex : ∀ PP ∈ Pg ∪ Q, ∃ s : 𝓞 D.host.F,
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ PP.asIdeal ∧ s ∉ w.asIdeal := by
    intro PP hPP
    by_contra hcon
    push_neg at hcon
    apply hne PP hPP
    have hle : (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal ≤ w.asIdeal := by
      intro s hs
      exact hcon s hs
    exact HeightOneSpectrum.ext
      ((HeightOneSpectrum.isMaximal _).eq_of_le w.isPrime.ne_top hle)
  choose! tf htf1 htf2 using hex
  refine ⟨∏ PP ∈ Pg ∪ Q, tf PP, ?_, ?_⟩
  · have : ∏ PP ∈ Pg ∪ Q, tf PP ∈ w.asIdeal.primeCompl :=
      Submonoid.prod_mem _ (fun c hc => htf2 c hc)
    exact this
  · have hmem : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ PP ∈ Pg ∪ Q, tf PP)
        ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
      rw [map_prod]
      exact Ideal.prod_mem_prod (fun PP hPP => algebraMap_mem_conjI (D := D) _ _ (htf1 PP hPP))
    have h1 := hu _ (algebraMap_mem_conjI (D := D) _ _ hmem)
    exact Submodule.smul_le_right h1

end GlobalTheory.TrOffShift
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiplier_shifted_lattice_away_from_places : ∀ (D : D7) (r : ℕ) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (L : Lt D.host.E r) (w : HeightOneSpectrum (𝓞 D.host.F)), (∀ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → ∀ u ∈ idq (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) L, ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • u ∈ L := by
  first | exact @GlobalTheory.TrOffShift.shift_mult | exact GlobalTheory.TrOffShift.shift_mult | (intros; apply GlobalTheory.TrOffShift.shift_mult <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel.TrOff

section Help
variable {D : D7} {S T : HSp D}

theorem partAt_add (c : AE D) (x y : WO S T) :
    GlobalTheory.LiftLevel.partAt c (x + y) = GlobalTheory.LiftLevel.partAt c x + GlobalTheory.LiftLevel.partAt c y :=
  Matrix.ext fun i j => mul_add c (x i j) (y i j)

theorem partAt_zero (c : AE D) : GlobalTheory.LiftLevel.partAt c (0 : WO S T) = 0 :=
  Matrix.ext fun _ _ => mul_zero c

theorem partAt_neg (c : AE D) (x : WO S T) : GlobalTheory.LiftLevel.partAt c (-x) = -GlobalTheory.LiftLevel.partAt c x :=
  Matrix.ext fun i j => mul_neg c (x i j)

noncomputable def gm (S T : HSp D) (γ : Af D.host.F) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : WO S T :=
  Matrix.of fun a k => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] y k a

theorem gm_add (γ : Af D.host.F) (x y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    gm S T γ (x + y) = gm S T γ x + gm S T γ y :=
  Matrix.ext fun a k => TensorProduct.tmul_add _ (x k a) (y k a)

theorem gm_zero (γ : Af D.host.F) : gm S T γ 0 = 0 :=
  Matrix.ext fun a k => TensorProduct.tmul_zero _ _

theorem gm_neg (γ : Af D.host.F) (x : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    gm S T γ (-x) = -gm S T γ x :=
  Matrix.ext fun a k => TensorProduct.tmul_neg _ (x k a)

theorem partAt_gm (σ α : Af D.host.F) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    GlobalTheory.LiftLevel.partAt (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)) (gm S T α y) =
      gm S T ((1 - σ) * α) y := by
  refine Matrix.ext fun a k => ?_
  change (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)) * ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a) =
    (pairA D.host.F 0 ((1 - σ) * α)) ⊗ₜ[D.host.F] y k a
  rw [sub_mul, one_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    ← TensorProduct.sub_tmul]
  congr 1
  refine Prod.ext ?_ ?_
  · change (0 : Ainf D.host.F) - _ * 0 = 0
    rw [mul_zero, sub_zero]
  · change α - σ * α = (1 - σ) * α
    ring

end Help

theorem mem_stdL_int {E : Type} [Field E] [NumberField E] {n : ℕ} (v : Fin n → E) :
    v ∈ stdL E n ↔ ∀ a, IsIntegral ℤ (v a) := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      intro a
      show IsIntegral ℤ ((Pi.single b 1 : Fin n → E) a)
      by_cases h : a = b
      · subst h; rw [Pi.single_eq_same]; exact isIntegral_one
      · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
    | zero => intro a; exact isIntegral_zero
    | add x y _ _ hx hy => intro a; exact (hx a).add (hy a)
    | smul c x _ hx => intro a; exact (c.2).mul (hx a)
  · intro h
    have e : v = ∑ a, (⟨v a, h a⟩ : 𝓞 E) • (Pi.single a 1 : Fin n → E) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · rw [Pi.smul_apply, Pi.single_eq_same]
        change v i = v i * 1
        rw [mul_one]
      · intro b _ hb
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [e]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem star_stdL : ∀ (D : D7) (n : ℕ) (v : Fin n → D.host.E), v ∈ stdL D.host.E n ↔ star v ∈ stdL D.host.E n := by
  intro D n v
  rw [mem_stdL_int, mem_stdL_int]
  refine forall_congr' fun a => ?_
  change _ ↔ IsIntegral ℤ (star (v a))
  exact ⟨fun h => h.map (starRingEnd D.host.E).toIntAlgHom, fun h => by
    have := h.map (starRingEnd D.host.E).toIntAlgHom
    rwa [show (starRingEnd D.host.E).toIntAlgHom (star (v a)) = v a from star_star (v a)] at this⟩

theorem rowTriv : ∀ (D : D7) (S T : HSp D) (k₀ : GA D S) (f : AE D), 0 < T.rank → f * f = f → (∀ x : WO S T, IsHalf f x → actO S T k₀ 1 x = x) → ∀ i j, f * (mt S k₀⁻¹ - 1) i j = 0 := by
  intro D S T k₀ f hT hf h i j
  let i₀ : Fin T.rank := ⟨0, hT⟩
  let x : WO S T := Matrix.of fun a b => if a = i₀ ∧ b = i then f else 0
  have hx : IsHalf f x := fun a b => by
    simp only [x, Matrix.of_apply]
    split_ifs
    · exact hf
    · exact mul_zero f
  have h1 := congrFun (congrFun (h x hx) i₀) j
  unfold actO at h1
  rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul, Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · simp only [x, Matrix.of_apply, true_and, if_true] at h1
    rw [Matrix.sub_apply, mul_sub, h1, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  · intro b _ hb
    simp [x, hb]
  · intro hi; exact absurd (Finset.mem_univ i) hi

end GlobalTheory.LiftLevel.TrOff

namespace GlobalTheory.LiftLevel

open GlobalTheory.LiftLevel.TrOff in

theorem partAt_off_mem_latO : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' hab hmover hgen hIsMov Lv hLv u hu
  by_cases hT : T.rank = 0
  · have h0 : GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u = 0 := Matrix.ext fun i _ => absurd i.2 (by omega)
    rw [h0]; exact zero_mem _
  have hTpos : 0 < T.rank := Nat.pos_of_ne_zero hT
  obtain ⟨σ, hσ, hσ0, hσ1⟩ := GlobalTheory.T.exists_finiteAdele_of_splitPlaces_idempotentSum D _ e he
  have hf : 1 - e - cA D e = 1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) := by rw [hσ]; ring
  have hgg : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)
      = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) := by
    rw [hσ]; exact (GlobalTheory.IdemConjSum.idemSum_add_conj_idem _ e he).1
  have hff : (1 - e - cA D e) * (1 - e - cA D e) = 1 - e - cA D e := by
    rw [hf]; linear_combination hgg
  have hrow := rowTriv D S T k₀ (1 - e - cA D e) hTpos hff hmover.2.1
  rw [hf] at hrow
  have hstar : ∀ v, v ∈ stdL D.host.E S.rank ↔ star v ∈ stdL D.host.E S.rank := star_stdL D S.rank
  rw [GlobalTheory.Ker.LatTens.latO_eq_hatA D S T C _ _ ΛT C.X.Λ hstar hAA]
  have hO : ∀ (c : 𝓞 D.host.F), ∀ y ∈ tens (stdL D.host.E S.rank) C.X.Λ,
      (algebraMap D.host.F D.host.E (c : D.host.F)) • y ∈ tens (stdL D.host.E S.rank) C.X.Λ := fun c y hy =>
    GlobalTheory.Ker.HatLat.smul_mem_tens _ _ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) hy
  have hgen' : ∀ α ∈ intAf D.host.F, ∀ y ∈ tens Λ' (Lv.sh C.X.Λ),
      gm S T ((1 - σ) * α) y ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) := by
    intro α hα y hy
    have hγ : (1 - σ) * α ∈ intAf D.host.F := by
      intro w
      rw [map_mul, map_sub, map_one]
      by_cases hw : ∃ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP = w
      · obtain ⟨PP, hPP, rfl⟩ := hw
        rw [hσ1 PP hPP, sub_self, zero_mul]; exact zero_mem _
      · push_neg at hw
        rw [hσ0 w hw, sub_zero, one_mul]; exact hα w
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, u', hu', rfl⟩ := hy
      refine GlobalTheory.T.mem_completedMatrixGroup_of_local_multiplier D S T _ hO _ hγ _ fun w => ?_
      by_cases hw : ∃ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP = w
      · left
        obtain ⟨PP, hPP, rfl⟩ := hw
        rw [map_mul, map_sub, map_one, hσ1 PP hPP, sub_self, zero_mul]
      · right
        push_neg at hw
        obtain ⟨t₁, ht₁, h1⟩ := GlobalTheory.T.exists_multiplier_standard_lattice_of_mover_trivial D S k₀ Λ' σ w (hσ0 w hw) hrow hIsMov v hv
        have hu'' : u' ∈ idq (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) C.X.Λ := by
          have : Lv.sh C.X.Λ = idq Lv.𝔪 (conjI Lv.𝔪) C.X.Λ := rfl
          rw [this, hLv] at hu'; exact hu'
        obtain ⟨t₂, ht₂, h2'⟩ := GlobalTheory.T.exists_multiplier_shifted_lattice_away_from_places D T.rank Pg Q C.X.Λ w hw u' hu''
        refine ⟨t₁ * t₂, fun hm => (w.isPrime.mem_or_mem hm).elim ht₁ ht₂, ?_⟩
        refine AddSubgroup.subset_closure ⟨_, h1, _, h2', ?_⟩
        refine Matrix.ext fun i j => ?_
        change algebraMap D.host.F D.host.E ((t₁ * t₂ : 𝓞 D.host.F) : D.host.F) * (v i * u' j) =
          algebraMap D.host.F D.host.E (t₁ : D.host.F) * v i * (algebraMap D.host.F D.host.E (t₂ : D.host.F) * u' j)
        rw [show ((t₁ * t₂ : 𝓞 D.host.F) : D.host.F) = (t₁ : D.host.F) * (t₂ : D.host.F) from rfl, map_mul]
        ring
    | zero => rw [gm_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [gm_add]; exact add_mem hx hy
    | neg x _ hx => rw [gm_neg]; exact neg_mem hx
  rw [hf]
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, y, hy, rfl⟩ := hw
    exact (partAt_gm σ α y).symm ▸ hgen' α hα y hy
  | zero => rw [partAt_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [partAt_add]; exact add_mem hx hy
  | neg x _ hx => rw [partAt_neg]; exact neg_mem hx

end GlobalTheory.LiftLevel

end
end
