import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpolyHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PProjOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PInvRoots
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPermOfMapEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PEigOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PDPairPol
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCxFlat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PGroupTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTraceSemi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PConjRep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHeckeTraceSemi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PPolyFnConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSpecConj

section
set_option autoImplicit false

open Polynomial

namespace UpperTheory.Gal.LocalSmoothExtension

theorem invPolProps_of (hR : InvRoots) : InvPolProps := by
  intro F _ _ P hP
  have hP0 : P ≠ 0 := fun h => hP (by simp [h])
  have hc : (P.coeff 0)⁻¹ ≠ 0 := inv_ne_zero hP
  have hrr : ∀ Q : F[X], Q.coeff 0 ≠ 0 → Q.reverse.reverse = Q := by
    intro Q hQ
    have hQd : Q.reverse.natDegree = Q.natDegree := by
      rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hQ), Nat.sub_zero]
    ext n
    rw [coeff_reverse, hQd, coeff_reverse, revAt_invol]
  have hdeg : P.reverse.natDegree = P.natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hP), Nat.sub_zero]
  refine ⟨?_, ?_, ?_⟩
  · unfold invPol
    rw [natDegree_C_mul hc, hdeg]
  · unfold invPol
    rw [mul_coeff_zero, coeff_C_zero, coeff_zero_reverse]
    exact mul_ne_zero hc (leadingCoeff_ne_zero.mpr hP0)
  · intro hs
    unfold invPol
    have hrs : P.reverse.Separable := by
      rw [PerfectField.separable_iff_squarefree]
      intro x hx
      obtain ⟨y, hy⟩ := hx
      have hx0 : x.coeff 0 ≠ 0 := by
        intro h0
        have h1 : P.reverse.coeff 0 = 0 := by
          rw [hy, mul_coeff_zero, mul_coeff_zero, h0, zero_mul, zero_mul]
        rw [coeff_zero_reverse] at h1
        exact leadingCoeff_ne_zero.mpr hP0 h1
      have hPx : x.reverse * x.reverse ∣ P := by
        refine ⟨y.reverse, ?_⟩
        rw [← hrr P hP, hy, reverse_mul_of_domain, reverse_mul_of_domain]
      have hu : IsUnit x.reverse := hs.squarefree _ hPx
      have hxd : x.natDegree = 0 := by
        have h1 : x.reverse.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
        rwa [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hx0), Nat.sub_zero] at h1
      rw [eq_C_of_natDegree_eq_zero hxd]
      exact isUnit_C.mpr (IsUnit.mk0 _ hx0)
    rw [mul_comm]
    exact hrs.mul_unit (isUnit_C.mpr (IsUnit.mk0 _ hc))

end UpperTheory.Gal.LocalSmoothExtension
end

section
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.listsEx_of :
    ListsEx := by
  intro F _ _ n χ hχ
  classical
  refine ⟨fun τ i => ((Polynomial.map τ χ).roots.toList).getD i 0, ?_⟩
  intro τ
  have hc : ((Polynomial.map τ χ).roots.toList).length = n := by
    rw [Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map, hχ]
  have hl : List.ofFn (fun i : Fin n => ((Polynomial.map τ χ).roots.toList).getD i 0)
      = (Polynomial.map τ χ).roots.toList := by
    apply List.ext_getElem
    · simp [hc]
    · intro i h1 h2
      simp [List.getElem?_eq_getElem h2]
  show (Polynomial.map τ χ).roots = _
  rw [Fin.univ_val_map, hl, Multiset.coe_toList]
end

section
open UpperTheory.Gal.LocalSmoothExtension

private theorem exists_perm_of_map_eq {n : ℕ} (a b : Fin n → ℂ)
    (h : Finset.univ.val.map a = Finset.univ.val.map b) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, b (e i) = a i :=
  _root_.UpperTheory.Reformulated.B.Qh57.exists_perm_of_map_eq a b h

theorem UpperTheory.Gal.LocalSmoothExtension.schWEq_of :
    SchWEq := by
  intro F _ _ n lam χ g hg
  have h : ∃ g : (F →+* ℂ) → Fin n → ℂ, Lists χ g := ⟨g, hg⟩
  unfold schW
  rw [dif_pos h]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨e, he⟩ := exists_perm_of_map_eq (h.choose τ) (g τ)
    ((h.choose_spec τ).symm.trans (hg τ))
  have hge : h.choose τ = g τ ∘ e := funext fun i => (he i).symm
  rw [hge]
  unfold UpperTheory.Gal.Schur.sch
  rw [← MvPolynomial.aeval_rename, GroundTheory.Heights₂.Heights.RestTerms.Schur.schur_isSymmetric (lam τ) e]
end

section
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.rootW_of :
    UpperTheory.Gal.W2.RootSumW → UpperTheory.Gal.W2.RootSumWOff → ListsEx → SchWEq → RootW := by
  intro hW hOff hL hS F _ _ n t₀ ε lam h hconj hexp
  rcases hexp with ⟨m, hm, hh⟩ | ⟨m, hm, hh⟩
  · obtain ⟨k₀, hk⟩ := hW F n t₀ ε lam m hconj hm
    refine ⟨k₀, fun k hk' => ?_⟩
    obtain ⟨c, hc, hsum⟩ := hk k hk'
    refine ⟨c, hc, ?_⟩
    intro χ hdeg hsep _ _ y
    obtain ⟨g, hg⟩ := hL F n χ hdeg
    rw [hsum χ g hsep hg y, hS F n lam χ g hg]
    simp only [hh, pow_add, Finset.mul_sum]
  · obtain ⟨k₀, hk⟩ := hOff F n t₀ ε lam m hconj hm
    refine ⟨k₀, fun k hk' => ?_⟩
    obtain ⟨c, hc, hsum⟩ := hk k hk'
    refine ⟨c, hc, ?_⟩
    intro χ hdeg hsep h0 hq y
    obtain ⟨g, hg⟩ := hL F n χ hdeg
    rw [hsum χ g hsep hg h0 hq y, hS F n lam χ g hg]
    simp only [hh, pow_add, Finset.mul_sum]
end

section
set_option autoImplicit false

namespace UpperTheory.Gal.LocalSmoothExtension

theorem hExpInj_of : HExpInj := by
  intro F _ _ n t₀ ε lam h hanti hh i k hik
  rcases hh with ⟨m, -, hh⟩ | ⟨m, -, hh⟩
  · rw [hh i, hh k] at hik
    have hi := i.isLt
    have hk := k.isLt
    rcases lt_trichotomy i k with hlt | heq | hgt
    · have hle := hanti t₀ hlt.le
      have hlt' : (i : ℕ) < k := hlt
      exfalso
      omega
    · exact heq
    · have hle := hanti t₀ hgt.le
      have hgt' : (k : ℕ) < i := hgt
      exfalso
      omega
  · rw [hh i, hh k] at hik
    have si : ∑ j ∈ Finset.univ.erase i, lam (NumberField.ComplexEmbedding.conjugate t₀) j +
        lam (NumberField.ComplexEmbedding.conjugate t₀) i =
        ∑ j, lam (NumberField.ComplexEmbedding.conjugate t₀) j :=
      Finset.sum_erase_add _ _ (Finset.mem_univ i)
    have sk : ∑ j ∈ Finset.univ.erase k, lam (NumberField.ComplexEmbedding.conjugate t₀) j +
        lam (NumberField.ComplexEmbedding.conjugate t₀) k =
        ∑ j, lam (NumberField.ComplexEmbedding.conjugate t₀) j :=
      Finset.sum_erase_add _ _ (Finset.mem_univ k)
    rcases lt_trichotomy i k with hlt | heq | hgt
    · have hle := hanti (NumberField.ComplexEmbedding.conjugate t₀) hlt.le
      have hlt' : (i : ℕ) < k := hlt
      exfalso
      omega
    · exact heq
    · have hle := hanti (NumberField.ComplexEmbedding.conjugate t₀) hgt.le
      have hgt' : (k : ℕ) < i := hgt
      exfalso
      omega

end UpperTheory.Gal.LocalSmoothExtension
end

section
open UpperTheory.Gal.LocalSmoothExtension

open scoped Classical in
private lemma hexp_finite {F : Type} [Field F] [NumberField F] {n : ℕ} (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ)
    (lam : (F →+* ℂ) → Fin n → ℕ) : {h : Fin n → ℕ | IsHExp t₀ ε lam h}.Finite := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Set.toFinite _
  · let i₀ : Fin n := ⟨0, hn⟩
    let c : ℕ := ∑ τ ∈ (Finset.univ.erase t₀).erase (NumberField.ComplexEmbedding.conjugate t₀),
      ε τ * ∑ j, lam τ j
    let h₁ : Fin n → ℕ := fun i => ((n - 1) * lam (NumberField.ComplexEmbedding.conjugate t₀) i₀ + c) +
      (lam t₀ i + (n - 1 - (i : ℕ)))
    let h₂ : Fin n → ℕ := fun i => (lam t₀ i₀ + c) +
      (∑ j ∈ Finset.univ.erase i, lam (NumberField.ComplexEmbedding.conjugate t₀) j + (i : ℕ))
    refine (Set.toFinite ({h₁, h₂} : Set (Fin n → ℕ))).subset ?_
    rintro h (⟨m, hm, hh⟩ | ⟨m, hm, hh⟩)
    · left
      funext i
      rw [hh i, ← hm i₀]
    · right
      funext i
      rw [hh i, ← hm i₀]

theorem UpperTheory.Gal.LocalSmoothExtension.unifBound_of :
    UnifBound := by
  intro F _ _ n I _ t ε lam κ
  have hb : ∀ (π : (F →+* ℂ) → (F →+* ℂ)) (i : I), ∃ b, ∀ h : Fin n → ℕ,
      IsHExp (t i) ε (fun τ => lam (π τ)) h → κ (fun τ => lam (π τ)) i h ≤ b := by
    intro π i
    obtain ⟨b, hb⟩ := ((hexp_finite (t i) ε (fun τ => lam (π τ))).image
      (κ (fun τ => lam (π τ)) i)).bddAbove
    exact ⟨b, fun h hh => hb ⟨h, hh, rfl⟩⟩
  choose b hb using hb
  obtain ⟨k, hk⟩ := Finite.exists_le (fun q : ((F →+* ℂ) → (F →+* ℂ)) × I => b q.1 q.2)
  refine ⟨k, fun σ i h hh => ?_⟩
  exact (hb (fun τ => (σ.symm : ℂ →+* ℂ).comp τ) i h hh).trans
    (hk ((fun τ => (σ.symm : ℂ →+* ℂ).comp τ), i))
end

section
set_option autoImplicit false

noncomputable section

open Matrix Polynomial
open UpperTheory.Gal.W2 (lefTerm)

namespace UpperTheory.Gal.LocalSmoothExtension

theorem lefSum_of : LefSum := by
  intro d A y
  set p : ℂ[X] := (1 + (X : ℂ[X]) • A.map (C : ℂ →+* ℂ[X])).det with hp
  have hdeg : p.natDegree < d + 1 := by
    have h1 : (1 + (X : ℂ[X]) • A.map (C : ℂ →+* ℂ[X]) : Matrix (Fin d) (Fin d) ℂ[X]) =
        (X : ℂ[X]) • A.map C + (1 : Matrix (Fin d) (Fin d) ℂ).map C := by
      rw [Matrix.map_one C (map_zero _) (map_one _), add_comm]
    have hle := natDegree_det_X_add_C_le A 1
    rw [← h1, Fintype.card_fin] at hle
    exact Nat.lt_succ_of_le hle
  have hev : p.eval (-y) = (1 - y • A).det := by
    rw [hp, ← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.one_apply, coe_evalRingHom, smul_eq_mul]
    split_ifs <;> simp <;> ring
  unfold lefTerm
  rw [← hev, eval_eq_sum_range' hdeg, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end UpperTheory.Gal.LocalSmoothExtension
end
end

section
set_option autoImplicit false

open Polynomial

namespace UpperTheory.Gal.LocalSmoothExtension

theorem coeffOcc_of : CoeffOcc := by
  intro d n t c h hinj hc hEq i
  set P : ℂ[X] := ∑ a ∈ Finset.range (d + 1), C ((-1) ^ a * t a) * X ^ a with hPdef
  set Q : ℂ[X] := ∑ j, C c * X ^ (h j) with hQdef
  have hPQ : P = Q := by
    apply Polynomial.funext
    intro y
    simp only [hPdef, hQdef, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
    rw [← Finset.mul_sum, ← hEq y]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [neg_pow]
    ring
  have hQ : Q.coeff (h i) = c := by
    simp only [hQdef, finset_sum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [if_neg (fun e => hji (hinj e).symm), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hP : P.coeff (h i) = if h i ∈ Finset.range (d + 1) then (-1) ^ (h i) * t (h i) else 0 := by
    simp only [hPdef, finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
  intro ht
  rw [hPQ, hQ] at hP
  split_ifs at hP with hlt
  · rw [ht, mul_zero] at hP
    exact hc hP
  · exact hc hP

end UpperTheory.Gal.LocalSmoothExtension
end

section
set_option autoImplicit false

noncomputable section

open NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.W2 (rts)

namespace UpperTheory.Gal.LocalSmoothExtension

theorem markRoots_of : MarkRoots := by
  intro p _ D G L ha i₀ v hv hinv P hP
  obtain ⟨i, rfl⟩ := (L.sig v).1 hv
  have hi : i = i₀ := by
    have : Subsingleton (Fin D.a) := by rw [ha]; infer_instance
    exact Subsingleton.elim _ _
  subst hi
  set φ : G.F →+* ℂ := G.iotaC.comp (L.s i) with hφ
  have hφe : ∀ x : D.F, φ (L.e x) = D.tau i x := fun x => L.s_C i x
  have hcomp : (D.tau i).comp (L.e.symm : G.F →+* D.F) = φ := by
    ext x
    rw [RingHom.comp_apply, ← hφe]
    simp
  have hP' : (map (L.e.symm : G.F →+* D.F) P).coeff 0 ≠ 0 := by
    rw [coeff_map]
    simpa using hP
  have hR : rts (endPol L P) (D.tau i) = Multiset.map (fun z : ℂ => z⁻¹) (map φ P).roots := by
    show rts (invPol (map (L.e.symm : G.F →+* D.F) P)) (D.tau i) = _
    rw [hinv D.F _ hP' (D.tau i)]
    simp only [rts, Polynomial.map_map, hcomp]
  rw [hR]
  have hω : φ (L.e D.ω) = D.ρc := by rw [hφe]; exact D.tau_ω i
  have hρ : (starRingEnd ℂ) D.ρc ≠ D.ρc := by
    intro h
    obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : ℂ) = D.ρc := ⟨D.ρc.re, Complex.conj_eq_iff_re.mp h⟩
    have h0 := D.ρc_root
    rw [← hr] at h0
    have h1 : r ^ 2 - (D.tr : ℝ) * r + (D.nm : ℝ) = 0 := by
      have := congrArg Complex.re h0
      simpa [sq] using this
    have h2 : ((D.tr : ℝ) ^ 2 - 4 * (D.nm : ℝ)) < 0 := by exact_mod_cast D.disc_neg
    nlinarith [sq_nonneg (2 * r - (D.tr : ℝ))]
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
    refine Multiset.map_congr rfl (fun μ _ => ?_)
    simp [markOf, h, hω]
  · rw [h]
    have hmap : map (ComplexEmbedding.conjugate φ) P = map (starRingEnd ℂ) (map φ P) := by
      rw [Polynomial.map_map]
      rfl
    rw [hmap, (IsAlgClosed.splits (map φ P)).roots_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun μ _ => ?_)
    simp [markOf, h, hω, hρ]

end UpperTheory.Gal.LocalSmoothExtension
end
end

section
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.dSumCongr_of :
    DSumCongr := by
  classical
  intro p _ G wt wt' s hw K f r K' φ
  unfold GlobalTheory.LKDef.dSumIrr
  rw [mul_comm _ s, ← smul_eq_mul s, smul_finsum]
  refine finsum_congr (fun q => ?_)
  split_ifs
  · rw [smul_eq_mul, hw]
    ring
  · simp
end

section
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.cxLin_of :
    CxFlat → CxLin := by
  intro hflat p _ G v K m f a hfin A w c
  classical
  have hU : (⋃ i, {z : Σ q : GlobalTheory.LKCx.FCls G, PtsOf G v K q × GlobalTheory.LKCx.grp G (Quot.out q).β |
      Seen G v K (f i) z.1 z.2.1 z.2.2}).Finite := Set.finite_iUnion hfin
  have hS : ∀ i z, Seen G v K (f i) z.1 z.2.1 z.2.2 → z ∈ hU.toFinset := by
    intro i z hz
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.2 ⟨i, hz⟩
  have hS' : ∀ z, Seen G v K (∑ i, a i • f i) z.1 z.2.1 z.2.2 → z ∈ hU.toFinset := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hz
    rw [Finset.sum_apply] at h2
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
    refine hS i z ⟨h1, ?_, h3⟩
    intro h0
    apply hi
    simp [Pi.smul_apply, smul_eq_mul, h0]
  have hR : ∀ α i, GlobalTheory.RootSumWeights.cxTotalM G v (c α) K (f i) (Kp G) (oneP G) =
      ∑ z ∈ hU.toFinset, summ G v (c α) K (f i) z :=
    fun α i => hflat p G v (c α) K (f i) hU.toFinset (hS i)
  have hT : ∀ z, summ G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) z =
      ∑ i, a i * w.sum fun α r => r * summ G v (c α) K (f i) z := by
    intro z
    unfold summ
    split_ifs with hfix
    · simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro α _
      ring
    · simp [Finsupp.sum]
  calc GlobalTheory.RootSumWeights.cxTotalM G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) (Kp G) (oneP G)
      = ∑ z ∈ hU.toFinset, summ G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) z :=
        hflat p G v _ K _ hU.toFinset hS'
    _ = ∑ z ∈ hU.toFinset, ∑ i, a i * w.sum fun α r => r * summ G v (c α) K (f i) z :=
        Finset.sum_congr rfl fun z _ => hT z
    _ = ∑ i, ∑ z ∈ hU.toFinset, a i * w.sum fun α r => r * summ G v (c α) K (f i) z := Finset.sum_comm
    _ = ∑ i, a i * w.sum fun α r => r * GlobalTheory.RootSumWeights.cxTotalM G v (c α) K (f i) (Kp G) (oneP G) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        simp only [Finsupp.sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [hR α i, Finset.mul_sum]
end

section
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.testOf_of :
    TestOf := by
  intro H _ K f hf
  obtain ⟨hbi, S, hS⟩ := hf
  have hinv : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g :=
    fun k hk k' hk' g => hbi ⟨k, hk⟩ ⟨k', hk'⟩ g
  refine ⟨⟨Subgroup.Commensurable.refl K, ?_, ?_, S, ?_⟩, hinv⟩
  · rintro x ⟨y, hy, rfl⟩
    exact hy
  · intro k hk g
    exact hinv _ (K.inv_mem hk) _ hk g
  · intro g hg
    obtain ⟨s, hs, a, b, rfl⟩ := hS g hg
    exact ⟨s, hs, a, a.2, b, b.2, rfl⟩
end

section
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.testOne_of :
    TestOne := by
  intro p _ G
  refine ⟨?_, ?_⟩
  · exact GlobalTheory.LKMid.isTest_indicator _ _ (by
      rintro _ ⟨k, hk, rfl⟩
      rw [GlobalTheory.LKCx.sigG_one]
      exact hk)
  · exact GlobalTheory.LKDef.HeckeTraceExample.indicator_bi _
end

section
open UpperTheory.Gal.LocalSmoothExtension
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

private lemma map_oneP (σ : ℂ ≃+* ℂ) {p : ℕ} [Fact p.Prime] (G : HTGroup p) (g : Gr G 1) :
    σ (oneP G g) = oneP G g := by
  unfold oneP
  by_cases h : g ∈ (Kp G : Set (Gr G 1))
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

private lemma pointSum_conj (σ : ℂ ≃+* ℂ) {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁)
    (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f : G₁ → ℂ)
    (φ : G₂ → ℂ) (hφ : ∀ x, σ (φ x) = φ x) :
    GlobalTheory.LKCount.pointSum ι₁ ι₂ θ K₁ K₂ γ δ (fun g => σ (f g)) φ =
      σ (GlobalTheory.LKCount.pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ) := by
  unfold GlobalTheory.LKCount.pointSum
  refine Eq.trans ?_ (AddEquiv.map_finsum σ.toAddEquiv _).symm
  refine finsum_congr fun q => ?_
  simp [map_mul, map_inv₀, map_natCast, hφ]

private lemma orbC_conj (σ : ℂ ≃+* ℂ) {H : Type} [Group H] (θ : H →* H) (K C : Subgroup H) (δ : H) (F : H → ℂ) :
    GlobalTheory.LKCount.orbC θ K C δ (fun g => σ (F g)) = σ (GlobalTheory.LKCount.orbC θ K C δ F) := by
  unfold GlobalTheory.LKCount.orbC
  refine Eq.trans ?_ (AddEquiv.map_finsum σ.toAddEquiv _).symm
  refine finsum_congr fun q => ?_
  simp [map_mul, map_inv₀, map_ratCast]

theorem UpperTheory.Gal.LocalSmoothExtension.goodConj_of :
    GoodConj := by
  intro σ p _ G K f h
  refine ⟨fun g hg => h.reg g fun h0 => hg (by simp [h0]), fun P hm hi => ?_, fun B x t hx y hy => ?_⟩
  · have h0 := h.pairs P hm hi
    unfold Pair.term at h0 ⊢
    split_ifs at h0 ⊢ with hh
    · unfold Pair.termAt at h0 ⊢
      rw [pointSum_conj σ _ _ _ _ _ _ _ f _ (map_oneP σ G), h0, map_zero]
    · rfl
  · have h0 := h.forms B x t hx y hy
    unfold GlobalTheory.LKCount.orbK at h0 ⊢
    have e : (fun h : G.GAf × Gr G 1 => σ (f h.1) * oneP G h.2) =
        fun h : G.GAf × Gr G 1 => σ (f h.1 * oneP G h.2) := by
      funext h
      rw [map_mul, map_oneP]
    rw [e, orbC_conj σ, h0, map_zero]
end

section
open UpperTheory.Gal.LocalSmoothExtension

open Polynomial in
private lemma roots_map_sigma (σ : ℂ ≃+* ℂ) (p : ℂ[X]) :
    (p.map (σ : ℂ →+* ℂ)).roots = p.roots.map (σ : ℂ →+* ℂ) :=
  (IsAlgClosed.splits p).roots_map _

private lemma sigma_sch (σ : ℂ ≃+* ℂ) {n : ℕ} (μ : Fin n → ℕ) (x : Fin n → ℂ) :
    σ (UpperTheory.Gal.Schur.sch μ x) = UpperTheory.Gal.Schur.sch μ (fun i => σ (x i)) := by
  unfold UpperTheory.Gal.Schur.sch
  exact MvPolynomial.comp_aeval_apply (φ := (σ : ℂ →+* ℂ).toRatAlgHom) x _

theorem UpperTheory.Gal.LocalSmoothExtension.schWConj_of :
    SchWEq → SchWConj := by
  intro hE σ F _ _ n lam χ
  classical
  by_cases h : ∃ g : (F →+* ℂ) → Fin n → ℂ, Lists χ g
  · obtain ⟨g, hg⟩ := h
    have hg' : Lists χ (fun τ i => σ (g ((σ.symm : ℂ →+* ℂ).comp τ) i)) := by
      intro τ
      have h1 : χ.map τ = (χ.map ((σ.symm : ℂ →+* ℂ).comp τ)).map (σ : ℂ →+* ℂ) := by
        rw [Polynomial.map_map]
        congr 1
        ext x
        simp
      have h2 := hg ((σ.symm : ℂ →+* ℂ).comp τ)
      unfold UpperTheory.Gal.W2.rts at h2 ⊢
      rw [h1, roots_map_sigma, h2, Multiset.map_map]
      rfl
    rw [hE F n (conjWt σ lam) χ _ hg', hE F n lam χ g hg, map_prod]
    let e : (F →+* ℂ) ≃ (F →+* ℂ) :=
      { toFun := fun τ => (σ.symm : ℂ →+* ℂ).comp τ
        invFun := fun τ => (σ : ℂ →+* ℂ).comp τ
        left_inv := fun τ => by ext x; simp
        right_inv := fun τ => by ext x; simp }
    refine Fintype.prod_equiv e _ _ fun τ => ?_
    rw [sigma_sch]
    rfl
  · have h0 : schW lam χ = 0 := by
      unfold schW
      exact dif_neg h
    have h1 : schW (conjWt σ lam) χ = 0 := by
      unfold schW
      exact dif_neg h
    rw [h0, h1, map_zero]
end

section
namespace UpperTheory.Gal.LocalSmoothExtension

theorem InvRoots_holds : InvRoots := invRoots_of
theorem InvPolProps_holds : InvPolProps := invPolProps_of InvRoots_holds
theorem RootW_holds : RootW :=
  rootW_of UpperTheory.Gal.W2.RootSumW_holds UpperTheory.Gal.W2.RootSumWOff_holds listsEx_of schWEq_of
theorem EigOf_holds : EigOf := eigOf_of UpperTheory.Gal.CertificateRingHomMap.pProjOne_holds
theorem CxLin_holds : CxLin := cxLin_of cxFlat_of
theorem GroupTop_of (h₁ : GlobalTheory.RootSumWeights.MarkWeightedFixedPointEqDefinitePairOdd) (h₂ : GlobalTheory.LKDef.TraceDefinitePairsEqAutomorphicTrace) : GroupTop :=
  groupTop_of h₁ h₂ RootW_holds InvRoots_holds InvPolProps_holds markRoots_of dPairPol_of dSumCongr_of testOf_of testOne_of
theorem HeckeTraceSemi_holds : HeckeTraceSemi := heckeTraceSemi_of traceSemi_of
theorem SpecConj_holds : SpecConj :=
  specConj_of traceSemi_of conjRep_of HeckeTraceSemi_holds goodConj_of (schWConj_of schWEq_of) polyFnConj_of

end UpperTheory.Gal.LocalSmoothExtension
end
