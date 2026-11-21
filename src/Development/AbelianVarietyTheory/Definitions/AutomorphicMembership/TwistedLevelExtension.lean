import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
import Formalism.LocalToGlobal.Columns.ChainTwKer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertAtLeCongN

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.TwModel
open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV

section
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))




theorem vq_lt : P.valuation E (qOf P : E) < 1 := by
  have : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have h := (P.valuation_lt_one_iff_mem (K := E) _).2 this
  simpa using h

theorem q_ne : (qOf P : E) ≠ 0 := by
  have : qOf P ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast this



def trv {n : ℕ} {a b : Fin n} (h : a ≠ b) : Sp E n ≃ₗ[E] Sp E n where
  toFun x := x + Pi.single a (x b)
  invFun x := x - Pi.single a (x b)
  map_add' x y := by simp only [Pi.add_apply, Pi.single_add]; abel
  map_smul' c x := by
    funext l
    by_cases hl : l = a
    · subst hl; simp [mul_add]
    · simp [Pi.single_eq_of_ne hl]
  left_inv x := by simp [Pi.single_eq_of_ne h.symm]
  right_inv x := by simp [Pi.single_eq_of_ne h.symm]

theorem trv_apply {n : ℕ} {a b : Fin n} (h : a ≠ b) (x : Sp E n) : trv h x = x + Pi.single a (x b) := rfl

theorem single_mem {n : ℕ} {a b : Fin n} (e : ℕ → ℤ) (he : e a ≤ e b) {x : Sp E n}
    (hx : x ∈ LocE.sclLat P (qOf P) n e) : (Pi.single a (x b) : Sp E n) ∈ LocE.sclLat P (qOf P) n e := by
  rw [ciMem_sclLat] at hx ⊢
  intro l
  rw [qth_intAt_iff]
  by_cases hl : l = a
  · subst hl
    have h1 := (qth_intAt_iff P _).1 (hx b)
    rw [Pi.single_eq_same]
    have hq := q_ne P
    have e1 : ((qOf P : E) ^ e l)⁻¹ * x b = (qOf P : E) ^ (e b - e l).toNat * (((qOf P : E) ^ e b)⁻¹ * x b) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_sub₀ hq]
      have := zpow_ne_zero (e b) hq
      field_simp
    rw [e1, map_mul, map_pow]
    exact mul_le_one' (pow_le_one' (vq_lt P).le _) h1
  · simp [Pi.single_eq_of_ne hl]



end

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (G : ChGlob X R.m) (m2 : ℕ)




end GlobalTheory.Mem.Col2.TC.TwModel

section Inhab

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.TC.TwModel

attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem exists_deep : ∃ (B : Base) (X : PreX B.toPre) (I : TC B X), StagesInhab.HasLetters B.toPre ∧ I.Ok ∧ TC.Pins B X ∧
    I.Deep ∧ ∀ a, (I.cst a).A = B.R.m := by
  classical
  obtain ⟨P, X, f, hL, hX, hsp, hdu, p1, p2⟩ := TrueColsTest.exists_pre
  obtain ⟨M, hM, -, -, m1, m2, -⟩ := FrameVal.frame_values P.R P.host _ f fun j τ => (P.hc τ).e_int j
  obtain ⟨α, hα, gα⟩ := @DatHecke.exists_gen M hM
  choose r hr using fun q : ℕ => IsAlgClosed.exists_pow_nat_eq (q : ℂ) (n := 2) two_pos
  obtain ⟨Y, hY, gY⟩ := InEx.exists_holds (2 * P.R.m) ({1, f.del, f.del'} : Set (Formalism.L2.Host.HChar P.host.E))
  obtain ⟨B, rfl, -, -, h2⟩ := BaseExt.exists_base P ∅ ∅
    (insert α (Y ∪ Finset.univ.image fun k => r (P.host.g k))) (by simp) (by simp)
    (fun z hz => by
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hα
      rcases Finset.mem_union.1 hz with h | h
      · exact hY z h
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 h
        exact IsAlgebraic.of_pow two_pos (by rw [hr]; exact isAlgebraic_natCast _))
  have i1 := gα B.LL B.embLL (h2 _ (Finset.mem_insert_self _ _))
  have hf : ({1, f.del, f.del'} : Set (Formalism.L2.Host.HChar B.host.E)).Finite := Set.toFinite _
  have ht : ∀ ξ ∈ ({1, f.del, f.del'} : Set (Formalism.L2.Host.HChar B.host.E)), Chr.IsTwist B.host (InEx.avoid B.toPre) ξ :=
    fun ξ hξ => InEx.isTwist_of_mem_set B f (Top.TwDat.untw B ∅) ξ (.inl hξ)
  obtain ⟨sel, hsel⟩ := Formalism.L2.Col.exists_sel B.fields
  obtain ⟨J, hJ⟩ := exists_ambIn_ok B.host
  obtain ⟨I, a1, -, -, -, -, -, a7⟩ := InEx.exists_colIn B X f hX hsp hdu (InEx.avoid B.toPre)
    (fun u => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Exists.intro u rfl))))), B.T_ne_pde u⟩)
    (fun i => ⟨Or.inr (Or.inl (Exists.intro i rfl)), (B.host.pde_ne_g i).1.symm, (B.host.pde_ne_g i).2.symm⟩)
    (fun _ hp h => InEx.mem_avoid_of_dvd _ hp h)
    _ hf (.inl rfl) (.inr (.inl rfl)) (.inr (.inr rfl)) ht
    (fun ξ hξ => gY hf B.LL B.embLL
      (fun z hz => h2 z (Finset.mem_insert_of_mem (Finset.mem_union_left _ hz))) ξ hξ (ht ξ hξ).1)
    (fun j => InEx.valuesIn_of (m1 j) _ i1) (InEx.valuesIn_of m2 _ i1) (fun i => by
      obtain ⟨s, hs⟩ := h2 _ (Finset.mem_insert_of_mem
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
      exact ⟨s, B.embLL.injective (by rw [map_pow, hs, hr, map_natCast])⟩) sel hsel J hJ
  exact ⟨B, X, I, hL, a1, ⟨p1, p2⟩, fun a P hP => ((a7 a).2.2.2 P hP).ge, fun a => (a7 a).2.1⟩






end GlobalTheory.Mem.Col2.TC.TwModel

end Inhab

end
