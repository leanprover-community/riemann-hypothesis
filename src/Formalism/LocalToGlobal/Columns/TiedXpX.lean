import Formalism.LocalToGlobal.Columns.TiedXpU

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (hQ : PtSurj d)

theorem ufGL_tilMv (u : d.what₂.Word) (c : PCl d) :
    ufGL d.X.E (d.R.N d.R.m) (d.tilMv u c).1 = (d.tilGa u c).1 := by
  have h := vfi_ufGL_ratHom d.sp.cm (d.R.N d.R.m) (d.tilGa u c)
  have e : ratHom d.sp.cm (d.R.N d.R.m) (d.tilGa u c) = (d.tilMv u c).1 :=
    (ratEquiv d.sp.cm (d.R.N d.R.m)).apply_symm_apply _
  rw [e] at h
  exact h

theorem chi_ka (u : d.what₂.Word) (hM : TilMove a u) (c : PCl d) :
    ((((classAgreement a hS hH hQ u d.R.m le_rfl).lev.chi ((tilAd a hS hH hP hQ u hM).ka c))⁻¹ : ℂˣ) : ℂ) =
      d.σ₀ (((d.lev d.R.m).chr (d.tilMv u c).2 : d.X.Kˣ) : d.X.K) := by
  have h1 := xp_clsG_chi d.sp.cm d.hX d.hPr d.σ₀ u (d.lev d.R.m) (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m) (d.repr u d.R.m)
    (hQ u d.R.m) (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.spec c) (stepCrd a hS hH u d.R.m le_rfl)
    ((tilAd a hS hH hP hQ u hM).ka c) (hM c).choose.2
  have h2 : (classAgreement a hS hH hQ u d.R.m le_rfl).lev.chi ((tilAd a hS hH hP hQ u hM).ka c) =
      levTyp ((Units.map d.σ₀.toMonoidHom).comp (d.lev d.R.m).chr) (hM c).choose := h1
  rw [h2, ← map_inv, vfi_typ d.sp.cm d.σ₀ (d.lev d.R.m), inv_inv, (hM c).choose_spec.1]

theorem evz_core (u : d.what₂.Word) (c : PCl d) (s s' : FrS d.X d.σ₀ (d.R.N d.R.m))
    (h : IsTr (atInf (embAt d.σ₀ d.X.emb) (d.tilGa u c).1.1) s' s) :
    frMul d.σ₀ (ufGL d.X.E (d.R.N d.R.m) (d.tilMv u c).1)⁻¹ s = s' := by
  rw [ufGL_tilMv]
  exact vfi_frMul_of_isTr d.σ₀ _ s s' h

theorem evzTied (u : d.what₂.Word) (hM : TilMove a u)
    (W : CF.ValTied (D := d.colRec a) u (atTTied a hH u).eV d.R.m le_rfl (classAgreement a hS hH hQ u d.R.m le_rfl))
    (hW : ∀ s, (W.eY s).1 = s.1) :
    CF.EvzTie (tilAd a hS hH hP hQ u hM) W (tieEWz a u) := by
  intro φ c s s' hTr
  have hs : frMul d.σ₀ (ufGL d.X.E (d.R.N d.R.m) (d.tilMv u c).1)⁻¹ s = s' := by
    refine evz_core u c s s' fun τ => ?_
    have h := hTr τ
    have e1 := congrFun (hW s) τ
    have e2 := congrFun (hW s') τ
    have e3 := embT_eq a hH
    rw [e1, e2, e3] at h
    exact h
  refine Eq.trans ?_ (congrArg (fun t => t * φ (((d.colRec a).fm u).til c) s') (chi_ka a hS hH hP hQ u hM c).symm)
  refine Eq.trans ?_ (congrArg (fun t => d.σ₀ (((d.lev d.R.m).chr (d.tilMv u c).2 : d.X.Kˣ) : d.X.K) *
    φ (((d.colRec a).fm u).til c) t) hs)
  rfl

end Rec

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem xp_baseLb {N n : ℕ} (hN : N = n + 1) [NeZero N] [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (hB : BasePi ST π) :
    baseLb E N ST = (baseLb E n ∅).map ((padL E n N).restrictScalars (𝓞 E)) ⊔
      Submodule.span (𝓞 E) {(Pi.single (lastIdx N) (algebraMap (𝓞 E) E π) : Fin N → E)} := by
  have hlast : ∀ j : Fin N, ¬ (j : ℕ) < n → j = lastIdx N := fun j hj => Fin.ext (by
    have := j.2
    show (j : ℕ) = N - 1
    omega)
  have hlv : ¬ ((lastIdx N : Fin N) : ℕ) < n := by
    show ¬ N - 1 < n
    omega
  have hlt : ∀ i : Fin n, (i : ℕ) < N := fun i => by have := i.2; omega
  ext x
  rw [rll_mem_baseLb, Submodule.mem_sup]
  constructor
  · rintro ⟨r, hr, hP⟩
    obtain ⟨q, hq⟩ := (hB.dvd _).1 hP
    refine ⟨padL E n N (fun i => algebraMap (𝓞 E) E (r ⟨i, hlt i⟩)), Submodule.mem_map_of_mem (by
      rw [rll_mem_baseLb]
      exact ⟨fun i => r ⟨i, hlt i⟩, fun _ => rfl, fun P hP => absurd hP (Finset.notMem_empty P)⟩),
      q • (Pi.single (lastIdx N) (algebraMap (𝓞 E) E π) : Fin N → E),
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    funext j
    rw [Pi.add_apply, Pi.smul_apply, padL_apply]
    by_cases hj : (j : ℕ) < n
    · have hne : j ≠ lastIdx N := fun e => hlv (e ▸ hj)
      rw [dif_pos hj, Pi.single_eq_of_ne hne, smul_zero, add_zero]
      exact hr j
    · rw [dif_neg hj, zero_add, hlast j hj, Pi.single_eq_same, Algebra.smul_def, ← map_mul, mul_comm, ← hq]
      exact hr _
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨y', hy', rfl⟩ := hy
    rw [SetLike.mem_coe, rll_mem_baseLb] at hy'
    obtain ⟨r', hr', -⟩ := hy'
    obtain ⟨q, rfl⟩ := Submodule.mem_span_singleton.1 hz
    refine ⟨fun j => if h : (j : ℕ) < n then r' ⟨j, h⟩ else q * π, fun j => ?_, fun P hP => ?_⟩
    · show _ = padL E n N y' j + (q • (Pi.single (lastIdx N) (algebraMap (𝓞 E) E π) : Fin N → E)) j
      rw [Pi.smul_apply, padL_apply]
      beta_reduce
      by_cases hj : (j : ℕ) < n
      · have hne : j ≠ lastIdx N := fun e => hlv (e ▸ hj)
        rw [dif_pos hj, dif_pos hj, Pi.single_eq_of_ne hne, smul_zero, add_zero]
        exact hr' _
      · rw [dif_neg hj, dif_neg hj, zero_add, hlast j hj, Pi.single_eq_same, Algebra.smul_def, map_mul]
    · beta_reduce
      rw [dif_neg hlv]
      exact Ideal.mul_mem_left _ _ ((hB.dvd π).2 (dvd_refl π) P hP)

end Gen

section GenQ

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

theorem xp_clsG_Lb (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)
    (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.L) :
    (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.Lb = baseLb X.E n (Pr.vT u) := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  rfl

theorem xp_clsPG_Lb (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet X.E n (∅ : Finset (Pl X.E)) Pr.vGs)
    (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.N) :
    (clsPG hc σ₀ Λ s hS hs Q).lev.Lb = baseLb X.E n ∅ := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  rfl

end GenQ

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (hQ : PtSurj d)

theorem tilBaseLat (u : d.what₂.Word) : CF.TilBaseLat (tildeLatticeAgreement a hS hH hP u) (classAgreement a hS hH hQ u d.R.m le_rfl) := by
  have h1 := xp_clsG_Lb d.sp.cm d.hX d.hPr d.σ₀ u (d.lev d.R.m) (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m) (d.repr u d.R.m)
    (hQ u d.R.m) (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.spec c) (stepCrd a hS hH u d.R.m le_rfl)
  have h2 := xp_clsPG_Lb d.sp.cm d.σ₀ d.levP.inv d.reprP hP (fun c => (ptGSD (Pr := d.Pr) d.W d.levP).outSec.spec c)
    (crdPr a hS hH)
  have h3 := xp_baseLb (E := d.X.E) (N_m_succ d.R) (basePi_of_ok (Pr := d.Pr) d.hX d.hPr u)
  have h4 := iXc_eq a hS
  refine h1.trans (h3.trans ?_)
  refine congrArg (fun t => t ⊔ Submodule.span (𝓞 d.host.E) {d.z0 u}) ?_
  rw [← h2, ← h4]
  rfl

end Rec

end Formalism.L2.Col
end
end
