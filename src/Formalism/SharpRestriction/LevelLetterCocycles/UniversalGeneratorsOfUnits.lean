import Formalism.SharpRestriction.LevelLetterCocycles.KillWinFromCut
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LevLetEMul
import Formalism.SharpRestriction.LevelLetterCocycles.CoprimeFrobeniusUniformizerPowers
import Formalism.SharpRestriction.LevelLetterCocycles.PsCoprimeOf
import Formalism.SharpRestriction.LevelLetterCocycles.FinLev
import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower

section
namespace Formalism.MainNotions.UnusedSlot80.UGen

theorem span_le_card {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] {g : ℕ} (v : Fin g → M) (N : Submodule R M)
    (hN : N ≤ Submodule.span R (Set.range v)) :
    ∃ (g₀ : ℕ) (w : Fin g₀ → M), g₀ ≤ g ∧ (∀ i, w i ∈ N) ∧
      N = Submodule.span R (Set.range w) := by
  classical
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Finsupp.basisSingleOne : Module.Basis (Fin g) R (Fin g →₀ R))
    (N.comap (Finsupp.linearCombination R v))
  refine ⟨n, fun i => Finsupp.linearCombination R v (b i : Fin g →₀ R), ?_, ?_, ?_⟩
  · have h1 := Module.finrank_eq_card_basis b
    have h2 := Submodule.finrank_le (N.comap (Finsupp.linearCombination R v))
    have h3 := Module.finrank_eq_card_basis
      (Finsupp.basisSingleOne : Module.Basis (Fin g) R (Fin g →₀ R))
    simp only [Fintype.card_fin] at h1 h3
    omega
  · intro i
    exact (b i).2
  · have hb : Submodule.span R (Set.range fun i => ((b i : _) : Fin g →₀ R)) =
        N.comap (Finsupp.linearCombination R v) := by
      have e : (Set.range fun i => ((b i : _) : Fin g →₀ R)) =
          (N.comap (Finsupp.linearCombination R v)).subtype '' Set.range b := by
        ext x; simp
      rw [e, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
    have e2 : (Set.range fun i => Finsupp.linearCombination R v (b i : Fin g →₀ R)) =
        (Finsupp.linearCombination R v) '' Set.range fun i => ((b i : _) : Fin g →₀ R) := by
      ext x; simp
    rw [e2, ← Submodule.map_span, hb, Submodule.map_comap_eq,
      Finsupp.range_linearCombination, inf_eq_right.mpr hN]

private theorem mkQ_mem_span_of_mem_sup_lemma {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (P : Submodule R V) (u : ι → V) {x : V} (hx : x ∈ Submodule.span R (Set.range u) ⊔ P) :
    P.mkQ x ∈ Submodule.span R (Set.range fun i => P.mkQ (u i)) := by
  obtain ⟨a, ha, p, hp, rfl⟩ := Submodule.mem_sup.mp hx
  have hp0 : P.mkQ p = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hp
  rw [map_add, hp0, add_zero]
  have hle : (Submodule.span R (Set.range u)).map P.mkQ ≤
      Submodule.span R (Set.range fun i => P.mkQ (u i)) := by
    rw [Submodule.map_span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  exact hle (Submodule.mem_map_of_mem ha)

theorem gen_of_killer {R V : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup V] [Module R V] (Msub Psub Isub : Submodule R V) (hIM : Isub ≤ Msub)
    {ι : Type*} [Finite ι] (F : ι → V) (hfg : Msub ≤ Submodule.span R (Set.range F) ⊔ Psub)
    (lR t : R) {g : ℕ} (v : Fin g → V)
    (hK : ∀ f ∈ Isub, ∃ K : ℕ, (lR ^ K * t) • f ∈ Submodule.span R (Set.range v) ⊔ Psub)
    (hsat : ∀ K : ℕ, ∀ f ∈ Msub, (lR ^ K * t) • f ∈ Psub → f ∈ Psub) :
    ∃ (g₀ : ℕ) (J : Fin g₀ → V), g₀ ≤ g ∧ (∀ i, J i ∈ Isub) ∧
      ∀ f ∈ Isub, ∃ o : Fin g₀ → R, f - ∑ i, o i • J i ∈ Psub := by
  classical
  let W : Submodule R (V ⧸ Psub) := Submodule.span R (Set.range fun i => Psub.mkQ (v i))
  let B : ℕ → Submodule R (V ⧸ Psub) := fun K =>
    W.comap ((lR ^ K * t) • (LinearMap.id : (V ⧸ Psub) →ₗ[R] V ⧸ Psub))
  have hBmono : Monotone B := by
    intro K K' hKK' q hq
    change (lR ^ K * t) • q ∈ W at hq
    change (lR ^ K' * t) • q ∈ W
    have e : lR ^ K' * t = lR ^ (K' - K) * (lR ^ K * t) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hKK']
    rw [e, mul_smul]
    exact W.smul_mem _ hq
  have hmemB : ∀ f ∈ Isub, ∃ K, Psub.mkQ f ∈ B K := by
    intro f hf
    obtain ⟨K, hKf⟩ := hK f hf
    refine ⟨K, ?_⟩
    change (lR ^ K * t) • Psub.mkQ f ∈ W
    rw [← map_smul]
    exact mkQ_mem_span_of_mem_sup_lemma Psub v hKf
  have hIle : Isub.map Psub.mkQ ≤ Submodule.span R (Set.range fun i => Psub.mkQ (F i)) := by
    intro q hq
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hq
    exact mkQ_mem_span_of_mem_sup_lemma Psub F (hfg (hIM hf))
  haveI hT : IsNoetherian R (Submodule.span R (Set.range fun i => Psub.mkQ (F i))) :=
    isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range _))
  haveI hIN : IsNoetherian R (Isub.map Psub.mkQ) := isNoetherian_of_le hIle
  have hfgI : (Isub.map Psub.mkQ).FG :=
    (Submodule.fg_top _).mp (IsNoetherian.noetherian _)
  obtain ⟨S, hS⟩ := hfgI
  have hSB : ∀ x ∈ S, ∃ K, x ∈ B K := by
    intro x hx
    have hxI : x ∈ Isub.map Psub.mkQ := by
      rw [← hS]; exact Submodule.subset_span (Finset.mem_coe.mpr hx)
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hxI
    exact hmemB f hf
  choose! Kf hKf using hSB
  obtain ⟨K, hIB⟩ : ∃ K, Isub.map Psub.mkQ ≤ B K := by
    refine ⟨S.sup Kf, ?_⟩
    rw [← hS, Submodule.span_le]
    intro x hx
    exact hBmono (Finset.le_sup (Finset.mem_coe.mp hx)) (hKf x (Finset.mem_coe.mp hx))
  have hN : Isub.map ((lR ^ K * t) • Psub.mkQ) ≤
      Submodule.span R (Set.range fun i => Psub.mkQ (v i)) := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hy
    have h1 := hIB (Submodule.mem_map_of_mem hf)
    change (lR ^ K * t) • Psub.mkQ f ∈ W at h1
    rw [LinearMap.smul_apply]
    exact h1
  obtain ⟨g₀, w, hg₀, hwN, hNw⟩ := span_le_card (fun i => Psub.mkQ (v i)) _ hN
  have hJ : ∀ i, ∃ f ∈ Isub, ((lR ^ K * t) • Psub.mkQ) f = w i :=
    fun i => Submodule.mem_map.mp (hwN i)
  choose J hJI hJw using hJ
  refine ⟨g₀, J, hg₀, hJI, ?_⟩
  intro f hf
  have hφf : ((lR ^ K * t) • Psub.mkQ) f ∈ Submodule.span R (Set.range w) := by
    rw [← hNw]; exact Submodule.mem_map_of_mem hf
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (R := R)).mp hφf
  refine ⟨o, hsat K _ ?_ ?_⟩
  · apply hIM
    exact Isub.sub_mem hf (Isub.sum_mem fun i _ => Isub.smul_mem _ (hJI i))
  · have h0 : ((lR ^ K * t) • Psub.mkQ) (f - ∑ i, o i • J i) = 0 := by
      rw [map_sub, map_sum]
      simp only [map_smul, hJw]
      rw [ho, sub_self]
    rw [LinearMap.smul_apply, ← map_smul] at h0
    rw [← Submodule.Quotient.mk_eq_zero]
    exact h0

end Formalism.MainNotions.UnusedSlot80.UGen
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE
local notation "aev" => Polynomial.aeval (AlgHom.toLinearMap (W.γE W.gam) : Module.End O W.EE)

theorem numI_upd (H : ℕ → ℕ) (e s : ℕ) (hs : s < e) (x : ℤ) :
    numI W e (Function.update (fun t => -((H t : ℕ) : ℤ)) s x) = ps W s ^ x.toNat := by
  unfold numI
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs), Function.update_self]
  rw [Finset.prod_eq_one fun t ht => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]
    rw [show (-((H t : ℕ) : ℤ)).toNat = 0 by omega, pow_zero], mul_one]

theorem denI_upd (H : ℕ → ℕ) (e s : ℕ) (hs : s < e) (x : ℤ) :
    denI W e (Function.update (fun t => -((H t : ℕ) : ℤ)) s x) =
      ps W s ^ (-x).toNat * ∏ t ∈ (Finset.range e).erase s, ps W t ^ H t := by
  unfold denI
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun t ht => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase ht), neg_neg, Int.toNat_natCast]

theorem aev_fixed (P : Polynomial O) : ∀ z : W.EE, W.γE W.gam z = z → aev P z = P.eval 1 • z := by
  induction P using Polynomial.induction_on with
  | C c => intro z _; simp [Polynomial.aeval_C, Module.algebraMap_end_apply]
  | add p q hp hq => intro z hz; rw [map_add, LinearMap.add_apply, hp z hz, hq z hz,
      Polynomial.eval_add, add_smul]
  | monomial k c ih =>
    intro z hz
    rw [pow_succ, ← mul_assoc, Polynomial.aeval_mul, Module.End.mul_apply, Polynomial.aeval_X,
      AlgHom.toLinearMap_apply, hz, ih z hz]
    simp

theorem γE_const (a : ZMod n) (x : O) :
    W.γE W.gam (ιE (letE a) * algebraMap O W.EE x) = ιE (letE a) * algebraMap O W.EE x := by
  rw [map_mul, W.γE_ext, AlgHom.commutes]
  congr 2
  exact Formalism.MainNotions.UnusedSlot80.KL.γA_letE W W.gam a

theorem lE_eq (κ : ℕ) : lE W κ = algebraMap O W.EE (((PD.p : ℕ) : O) ^ κ) := by
  simp [lE]

def InvLevAt (s : ℕ) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ (a : ZMod n) (T : Finset ℕ) (e : ℕ → ℕ), s ∉ T →
    ∀ f : W.EE, InFr W a 1 (∏ t ∈ T, ps W t ^ e t) f →
    (∃ κ : ℕ, InFr W a (ps W s) (∏ t ∈ T, ps W t ^ e t) (lE W κ * (W.γE W.gam f - f))) →
    ∃ (κ : ℕ) (x : O), InFr W a (ps W s) (∏ t ∈ T, ps W t ^ e t)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE a) * algebraMap O W.EE x)

theorem invLevAt_of (h : CutU.InvLevCore W) (s : ℕ) : InvLevAt W s :=
  fun hCA h5 a T e hs f hf hγ => h hCA h5 a s T e hs f hf hγ

theorem lev_const (hKL : KillerLevCore W) (hS : PsStable W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : 5 ≤ PD.p) (a : ZMod n) (ell : ℕ) (H : ℕ → ℕ) (M : ℕ)
    (hM : ∀ s < ell, H s ≤ M) (y : W.EE) (hy : InId W a ell (fun t => -((H t : ℕ) : ℤ)) y)
    (s : ℕ) (hs : s < ell) (hInv : InvLevAt W s) :
    ∃ (κ : ℕ) (x : O), InId W a ell (Function.update (fun t => -((H t : ℕ) : ℤ)) s (H s))
      (lE W κ * PPγ W ell (Finset.Ico (-(M : ℤ)) M) y - ιE (letE a) * algebraMap O W.EE x) := by
  set α0 : ℕ → ℤ := fun t => -((H t : ℕ) : ℤ) with hα0
  set JS : Finset ℤ := Finset.Ico (-(M : ℤ)) M with hJS
  set Fp : ℤ → Polynomial O := fun i => Polynomial.X ^ (PD.p ^ ell) -
    Polynomial.C (((W.χΓ W.gam) ^ (i * (PD.p : ℤ) ^ ell) : Oˣ) : O) with hFp
  set Sg : Polynomial O := ∑ k ∈ Finset.range (PD.p ^ ell), Polynomial.X ^ k with hSg
  have hPP : PPO W ell JS = (∏ i ∈ JS.erase 0, Fp i) * Sg := rfl
  obtain ⟨-, hK⟩ := hKL hCA ell JS
  by_cases hH0 : H s = 0
  · refine ⟨0, 0, ?_⟩
    have e : Function.update α0 s ((H s : ℕ) : ℤ) = α0 := by
      rw [Function.update_eq_self_iff, hα0]; simp [hH0]
    rw [e, map_zero, mul_zero, sub_zero, lE, pow_zero, one_mul]
    exact inId_aeval W hS _ y hy
  have hH1 : 1 ≤ H s := Nat.one_le_iff_ne_zero.mpr hH0
  set Sm : Finset ℤ := Finset.Ico (-((H s : ℕ) : ℤ)) 0 with hSm
  set Sp : Finset ℤ := Finset.Ico 1 ((H s : ℕ) : ℤ) with hSp
  have hMs := hM s hs
  have hsub : Sm ∪ Sp ⊆ JS.erase 0 := by
    intro i hi
    simp only [Finset.mem_union, Finset.mem_Ico, hSm, hSp] at hi
    simp only [Finset.mem_erase, Finset.mem_Ico, hJS]
    omega
  have hdisj : Disjoint Sm Sp := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [Finset.mem_Ico, hSm, hSp] at h1 h2
    omega
  set Rest : Finset ℤ := JS.erase 0 \ (Sm ∪ Sp)
  have hPP' : PPO W ell JS = (∏ i ∈ Sp, Fp i) * (Sg * ((∏ i ∈ Sm, Fp i) * ∏ i ∈ Rest, Fp i)) := by
    rw [hPP, ← Finset.prod_sdiff hsub, Finset.prod_union hdisj]
    ring

  set y₁ := aev (∏ i ∈ Rest, Fp i) y with hy₁
  have hy₁m : InId W a ell α0 y₁ := inId_aeval W hS _ y hy

  obtain ⟨κ₁, h₁⟩ := (hK a α0 s hs y₁ hy₁m).2.2 (H s)
  have e1 : α0 s + ((H s : ℕ) : ℤ) = 0 := by simp [hα0]
  have e1' : Finset.Ico (α0 s) (α0 s + ((H s : ℕ) : ℤ)) = Sm := by rw [e1]
  rw [e1', e1] at h₁
  set y₂ := lE W κ₁ * aev (∏ i ∈ Sm, Fp i) y₁ with hy₂
  set α1 := Function.update α0 s 0 with hα1

  set Gg := aev Sg y₂ with hGg
  have hGm : InId W a ell α1 Gg := inId_aeval W hS _ y₂ h₁
  obtain ⟨κ₂, h₂⟩ := (hK a α1 s hs y₂ h₁).2.2 1
  have e2 : α1 s = 0 := by rw [hα1, Function.update_self]
  have hF0 : (∏ i ∈ Finset.Ico (α1 s) (α1 s + ((1 : ℕ) : ℤ)), Fp i) = Polynomial.X ^ (PD.p ^ ell) - 1 := by
    have hI : Finset.Ico (0 : ℤ) (0 + ((1 : ℕ) : ℤ)) = {0} := by ext i; simp; omega
    rw [e2, hI, Finset.prod_singleton]
    simp [hFp]
  rw [hF0, e2] at h₂
  have hupd1 : Function.update α1 s (0 + ((1 : ℕ) : ℤ)) = Function.update α0 s 1 := by
    rw [hα1, Function.update_idem]; norm_num
  rw [hupd1] at h₂
  have hγG : W.γE W.gam Gg - Gg = aev (Polynomial.X ^ (PD.p ^ ell) - 1 : Polynomial O) y₂ := by
    rw [← mul_geom_sum, aeval_mul_apply, ← hSg, ← hGg, map_sub, LinearMap.sub_apply,
      Polynomial.aeval_X, map_one, AlgHom.toLinearMap_apply, Module.End.one_apply]
  rw [← hγG] at h₂

  have hT : s ∉ (Finset.range ell).erase s := by simp
  have hGfr : InFr W a 1 (∏ t ∈ (Finset.range ell).erase s, ps W t ^ H t) Gg := by
    have := hGm
    unfold InId at this
    have en := numI_upd W H ell s hs 0
    have ed := denI_upd W H ell s hs 0
    simp only [numI, denI] at en ed
    rw [← hα0, ← hα1] at en ed
    rw [en, ed] at this
    simpa using this
  have hγfr : InFr W a (ps W s) (∏ t ∈ (Finset.range ell).erase s, ps W t ^ H t)
      (lE W κ₂ * (W.γE W.gam Gg - Gg)) := by
    have := h₂
    unfold InId at this
    have en := numI_upd W H ell s hs 1
    have ed := denI_upd W H ell s hs 1
    simp only [numI, denI] at en ed
    rw [← hα0] at en ed
    rw [en, ed] at this
    simpa using this
  obtain ⟨κ₃, x, hx⟩ := hInv hCA h5 a _ H hT Gg hGfr ⟨κ₂, hγfr⟩

  set Z := lE W κ₃ * Gg - ιE (letE a) * algebraMap O W.EE x with hZ
  set α2 := Function.update α0 s 1 with hα2
  have hZm : InId W a ell α2 Z := by
    unfold InId
    have en := numI_upd W H ell s hs 1
    have ed := denI_upd W H ell s hs 1
    simp only [numI, denI] at en ed
    rw [← hα0, ← hα2] at en ed
    rw [en, ed]
    simpa using hx
  obtain ⟨κ₄, h₄⟩ := (hK a α2 s hs Z hZm).2.2 (H s - 1)
  have e4 : α2 s + ((H s - 1 : ℕ) : ℤ) = ((H s : ℕ) : ℤ) := by
    rw [hα2, Function.update_self]; push_cast [Nat.cast_sub hH1]; ring
  have e4' : Finset.Ico (α2 s) (α2 s + ((H s - 1 : ℕ) : ℤ)) = Sp := by
    rw [e4, hα2, Function.update_self]
  rw [e4', e4, hα2, Function.update_idem] at h₄
  refine ⟨κ₄ + κ₃ + κ₁, ((PD.p : ℕ) : O) ^ κ₄ * (Polynomial.eval 1 (∏ i ∈ Sp, Fp i)) * x, ?_⟩
  convert h₄ using 1
  have hfix := aev_fixed W (∏ i ∈ Sp, Fp i) _ (γE_const W a x)
  have hmain : aev (∏ i ∈ Sp, Fp i) Gg = lE W κ₁ * PPγ W ell JS y := by
    rw [PPγ, hPP', aeval_mul_apply, aeval_mul_apply, aeval_mul_apply, ← hy₁, ← aeval_lE, ← aeval_lE,
      ← hy₂]
  rw [hZ, map_sub, aeval_lE, hmain, hfix, Algebra.smul_def, lE_eq, lE_eq, lE_eq, lE_eq]
  simp only [map_mul, map_pow, pow_add]
  ring

end Formalism.MainNotions.UnusedSlot80.UGen
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem crt_fam {ι : Type} [DecidableEq ι] (x₀ : LetA O n) (x : ι → LetA O n) (hx₀ : x₀ ∈ W.AΔ)
    (hx : ∀ i, x i ∈ W.AΔ) (s : Finset ι) (h0 : ∀ i ∈ s, Cop W x₀ (x i))
    (hp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Cop W (x i) (x j)) :
    ∃ κ : ℕ, ∃ r₀ ∈ W.AΔ, ∃ R : ι → LetA O n, (∀ i ∈ s, R i ∈ W.AΔ) ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ = (∏ i ∈ s, x i) * r₀ + ∑ i ∈ s, x₀ * (∏ j ∈ s.erase i, x j) * R i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, W.AΔ.one_mem, 0, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨κ, r₀, hr₀, R, hR, hsum⟩ := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj hij => hp i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
    have hQ : Cop W (x a) (x₀ * ∏ i ∈ s, x i) :=
      cop_symm W (cop_mul W hx₀ (hx a) (h0 a (Finset.mem_insert_self a s))
        (cop_prod W s x hx (hx a) fun i hi => hp i (Finset.mem_insert_of_mem hi) a
          (Finset.mem_insert_self a s) (fun h => ha (h ▸ hi))))
    obtain ⟨m, r, hr, t, ht, hm⟩ := hQ
    refine ⟨κ + m, r₀ * r, W.AΔ.mul_mem hr₀ hr,
      fun i => if i = a then Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ * t else R i * r, ?_, ?_⟩
    · intro i hi
      by_cases hia : i = a
      · simp only [hia, if_true]; exact W.AΔ.mul_mem (lA_mem W κ) ht
      · simp only [hia, if_false]
        exact W.AΔ.mul_mem (hR i ((Finset.mem_insert.1 hi).resolve_left hia)) hr
    · rw [Finset.sum_insert ha]
      dsimp only
      rw [if_pos rfl, Finset.erase_insert ha, Finset.prod_insert ha]
      have hs : ∑ i ∈ s, x₀ * (∏ j ∈ (insert a s).erase i, x j) *
          (if i = a then Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ * t else R i * r) =
          (∑ i ∈ s, x₀ * (∏ j ∈ s.erase i, x j) * R i) * r * x a := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hia : i ≠ a := fun h => ha (h ▸ hi)
        rw [if_neg hia, Finset.erase_insert_of_ne (Ne.symm hia),
          Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
        ring
      rw [hs, pow_add]
      linear_combination (r * x a) * hsum + Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ * hm


variable [IsDomain O]

theorem cop_pi_ps (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (s : ℕ) : Cop W W.π₀ (Formalism.MainNotions.ArcLiftingSetup.ps W s) := by
  obtain ⟨a, ha⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_π₀ hR s
  have haΔ : a ∈ W.AΔ := by
    refine Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ hR.1 (fun _ => Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_ne hR) ?_
    rw [← ha]; exact Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_AΔ s hR.1
  have e1 : Formalism.MainNotions.ArcLiftingSetup.ps W s - Formalism.MainNotions.ArcLiftingSetup.lA W = (W.φA ^ s) W.π₀ :=
    Formalism.MainNotions.UnusedSlot80.ToolsR.pS_sub s
  refine ⟨1, -a, W.AΔ.neg_mem haΔ, 1, W.AΔ.one_mem, ?_⟩
  linear_combination (-1 : LetA O n) * e1 - ha

variable [NeZero n]

theorem cop_ps_ps (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (s t : ℕ) (hst : s ≠ t) :
    Cop W (Formalism.MainNotions.ArcLiftingSetup.ps W s) (Formalism.MainNotions.ArcLiftingSetup.ps W t) := by
  obtain ⟨κ, a, ha, b, hb, e⟩ := Formalism.MainNotions.UnusedSlot80.KF.psCoprime_of W hR s t hst
  exact ⟨κ, a, ha, b, hb, e⟩

theorem crtLev (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (e : ℕ) (N : ℕ → ℕ) :
    ∃ κ : ℕ, ∃ u₀ ∈ W.AΔ, ∃ u : ℕ → LetA O n, (∀ s < e, u s ∈ W.AΔ) ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ = u₀ + ∑ s ∈ Finset.range e, u s ∧
      (∃ r ∈ W.AΔ, u₀ = (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ N t) * r) ∧
      ∀ s < e, ∃ r ∈ W.AΔ,
        u s = W.π₀ * (∏ t ∈ (Finset.range e).erase s, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ N t) * r := by
  have hps : ∀ t, Formalism.MainNotions.ArcLiftingSetup.ps W t ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hR.1
  have hx : ∀ t, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ N t ∈ W.AΔ := fun t => W.AΔ.pow_mem (hps t) _
  obtain ⟨κ, r₀, hr₀, R, hRm, hsum⟩ := crt_fam W W.π₀ (fun t => Formalism.MainNotions.ArcLiftingSetup.ps W t ^ N t) hR.1 hx
    (Finset.range e)
    (fun t _ => cop_symm W (cop_pow W (hps t) hR.1 (cop_symm W (cop_pi_ps W hR t)) (N t)))
    (fun i _ j _ hij => cop_pow W (hps i) (hx j)
      (cop_symm W (cop_pow W (hps j) (hps i) (cop_ps_ps W hR j i (Ne.symm hij)) (N j))) (N i))
  refine ⟨κ, _, W.AΔ.mul_mem (W.AΔ.prod_mem fun t _ => hx t) hr₀,
    fun s => W.π₀ * (∏ t ∈ (Finset.range e).erase s, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ N t) * R s,
    fun s hs => W.AΔ.mul_mem (W.AΔ.mul_mem hR.1 (W.AΔ.prod_mem fun t _ => hx t))
      (hRm s (Finset.mem_range.2 hs)), by dsimp only; exact hsum, ⟨r₀, hr₀, rfl⟩,
    fun s hs => ⟨R s, hRm s (Finset.mem_range.2 hs), rfl⟩⟩


end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE

theorem inId_sub {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} {f g : W.EE} (hf : InId W a e α f)
    (hg : InId W a e α g) : InId W a e α (f - g) := by
  have := inId_add W hf (inId_smul W hg (-1))
  convert this using 1
  simp [sub_eq_add_neg]

theorem inId_sum {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} (S : Finset ℕ) (f : ℕ → W.EE)
    (hf : ∀ i ∈ S, InId W a e α (f i)) : InId W a e α (∑ i ∈ S, f i) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, Subalgebra.zero_mem _, by simp⟩
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact inId_add W (hf i (Finset.mem_insert_self i S)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem piece_upd (H : ℕ → ℕ) (a : ZMod n) (e s : ℕ) (hs : s < e) (z r : LetA O n) (hr : r ∈ W.AΔ)
    (hz : z = ps W s ^ H s * r) :
    InId W a e (Function.update (fun t => -((H t : ℕ) : ℤ)) s (H s)) (ιE (letE a * z)) := by
  unfold InId
  have en := numI_upd W H e s hs (H s)
  have ed := denI_upd W H e s hs (H s)
  simp only [numI, denI] at en ed
  rw [en, ed]
  refine ⟨(∏ t ∈ (Finset.range e).erase s, ps W t ^ H t) * r,
    Subalgebra.mul_mem _ (Subalgebra.prod_mem _ fun t _ =>
      Subalgebra.pow_mem _ (Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) t) _) hr, ?_⟩
  rw [← map_mul, hz]
  congr 1
  simp only [Int.toNat_natCast, show (-((H s : ℕ) : ℤ)).toNat = 0 by omega, pow_zero, one_mul]
  ring

variable [IsDomain O]

theorem value0 (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (a : ZMod n) (z : LetA O n) (hz : z ∈ W.AΔ) :
    ∃ (o : O) (w : LetA O n), w ∈ W.AΔ ∧
      (letE a : LetA O n) * z = letE a * (algebraMap O (LetA O n) o + W.π₀ * w) := by
  obtain ⟨f, hf, -⟩ := hR.2.1 z hz
  set c := PowerSeries.constantCoeff (f a) with hc
  set g := PowerSeries.mk fun k => PowerSeries.coeff (k + 1) (f a) with hg
  have hfa : f a = g * PowerSeries.X + c • (1 : PowerSeries O) := by
    rw [PowerSeries.smul_eq_C_mul, mul_one, hg, hc]
    exact PowerSeries.eq_shift_mul_X_add_const (f a)
  have ha0 : PowerSeries.constantCoeff W.π₀₁ = 0 := Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR
  have hs0 := PowerSeries.HasSubst.of_constantCoeff_zero' ha0
  set w' : LetA O n := letE a * fun _ => PowerSeries.subst W.π₀₁ g with hw'
  have hza : z a = PowerSeries.subst W.π₀₁ g * W.π₀₁ + c • (1 : PowerSeries O) := by
    rw [hf a]
    change PowerSeries.subst W.π₀₁ (f a) = _
    rw [hfa, ← PowerSeries.coe_substAlgHom hs0, map_add, map_mul, PowerSeries.substAlgHom_X,
      map_smul, map_one]
  have key : (letE a : LetA O n) * z = letE a * (algebraMap O (LetA O n) c + W.π₀ * w') := by
    funext i
    by_cases hi : i = a
    · subst hi
      simp only [Pi.mul_apply, Pi.add_apply, letE, Pi.single_eq_same, one_mul, hw', hza,
        LocWach.π₀, Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply]
      ring
    · simp [letE, Pi.single_eq_of_ne hi, hw']
  refine ⟨c, w', ?_, key⟩
  refine Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ hR.1 (fun i => by
    show W.π₀₁ ≠ 0
    exact Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_ne hR) ?_
  have hidem : w' * letE a = w' := by
    rw [hw', mul_comm, ← mul_assoc, Formalism.MainNotions.UnusedSlot80.DivLevR.letE_idem]
  have e : W.π₀ * w' = letE a * z - letE a * algebraMap O (LetA O n) c := by
    rw [key]; linear_combination (-W.π₀) * hidem
  rw [e]
  exact W.AΔ.sub_mem (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.DivLevR.letE_mem a) hz)
    (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.DivLevR.letE_mem a) (W.AΔ.algebraMap_mem c))

theorem lE_add' (κ κ' : ℕ) : lE W (κ + κ') = lE W κ * lE W κ' := by simp [lE, pow_add]

theorem inId0_of_mem (H : ℕ → ℕ) (a : ZMod n) (e : ℕ) {z : LetA O n} (hz : z ∈ W.AΔ) :
    InId W a e (fun t => -((H t : ℕ) : ℤ)) (ιE (letE a * z)) := by
  unfold InId
  have h1 : (∏ s ∈ Finset.range e, ps W s ^ (-((H s : ℕ) : ℤ)).toNat) = 1 :=
    Finset.prod_eq_one fun s _ => by rw [show (-((H s : ℕ) : ℤ)).toNat = 0 by omega, pow_zero]
  rw [h1]
  refine ⟨(∏ s ∈ Finset.range e, ps W s ^ (-(-((H s : ℕ) : ℤ))).toNat) * z,
    Subalgebra.mul_mem _ (Subalgebra.prod_mem _ fun t _ =>
      Subalgebra.pow_mem _ (Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) t) _) hz, ?_⟩
  rw [← map_mul]; congr 1; ring

def Dv (H : ℕ → ℕ) (s : ℕ) (z : LetA O n) : Prop := ∃ r ∈ W.AΔ, z = ps W s ^ H s * r

theorem dv_add {H : ℕ → ℕ} {s : ℕ} {z z' : LetA O n} (h : Dv W H s z) (h' : Dv W H s z') :
    Dv W H s (z + z') := by
  obtain ⟨r, hr, rfl⟩ := h; obtain ⟨r', hr', rfl⟩ := h'
  exact ⟨r + r', W.AΔ.add_mem hr hr', by ring⟩

theorem dv_sum {H : ℕ → ℕ} {s : ℕ} (S : Finset ℕ) (f : ℕ → LetA O n) (hf : ∀ t ∈ S, Dv W H s (f t)) :
    Dv W H s (∑ t ∈ S, f t) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, W.AΔ.zero_mem, by simp⟩
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact dv_add W (hf i (Finset.mem_insert_self i S)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem dv_prod (H : ℕ → ℕ) (k : ℕ) (hk : 1 ≤ k) (S : Finset ℕ) (s : ℕ) (hs : s ∈ S) {r : LetA O n}
    (hr : r ∈ W.AΔ) : Dv W H s ((∏ t ∈ S, ps W t ^ (k * H t)) * r) := by
  have hps := Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W)
  refine ⟨ps W s ^ ((k - 1) * H s) * (∏ t ∈ S.erase s, ps W t ^ (k * H t)) * r,
    W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (hps s) _)
      (W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem (hps t) _)) hr, ?_⟩
  rw [← Finset.mul_prod_erase _ _ hs]
  have e : k * H s = H s + (k - 1) * H s := by
    have hk' : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
    conv_lhs => rw [hk']
    ring
  rw [e, pow_add]; ring

theorem lE_smul (κ : ℕ) (z : W.EE) : lE W κ * z = (((PD.p : ℕ) : O) ^ κ) • z := by
  rw [Algebra.smul_def, map_pow, map_natCast]; rfl

theorem killer_elem (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hKL : KillerLevCore W)
    (hS : PsStable W) (hRAT : CutU.RATCore W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : 5 ≤ PD.p) (A : ArcP n) (a : ZMod n) (e : ℕ) (M : ℕ)
    (hM : ∀ s < e, A.Hs a e s ≤ M) (hInv : ∀ s < e, InvLevAt W s) (κc : ℕ) (u₀ r₀ : LetA O n) (u rs : ℕ → LetA O n)
    (hr₀ : r₀ ∈ W.AΔ) (hrs : ∀ s < e, rs s ∈ W.AΔ)
    (hsum : lA W ^ κc = u₀ + ∑ s ∈ Finset.range e, u s)
    (hu₀ : u₀ = (∏ t ∈ Finset.range e, ps W t ^ (2 * A.Hs a e t)) * r₀)
    (hus : ∀ s < e, u s = W.π₀ * (∏ t ∈ (Finset.range e).erase s, ps W t ^ (2 * A.Hs a e t)) * rs s)
    (y : W.EE) (hy : InFr W a 1 (abelian₂ W A a e) y) :
    ∃ (K : ℕ) (x : ℕ → O) (x₀ : O), InFr W a (W.π₀ * abelian₂ W A a e) 1
      (lE W K * PPγ W e (Finset.Ico (-(M : ℤ)) M) y -
        ∑ s ∈ Finset.range e, x s • ιE (letE a * u s) - x₀ • ιE (letE a * (abelian₂ W A a e * r₀))) := by
  set H : ℕ → ℕ := A.Hs a e with hH
  set Λ := abelian₂ W A a e with hΛ
  set JS : Finset ℤ := Finset.Ico (-(M : ℤ)) M with hJS
  set α0 : ℕ → ℤ := fun t => -((H t : ℕ) : ℤ) with hα0
  have hps := Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W)
  have hΛm : Λ ∈ W.AΔ := W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem (hps t) _
  have hy0 : InId W a e α0 y := (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A a e y).1 hy
  have hlev := fun s (hs : s < e) => lev_const W hKL hS hCA h5 a e H M hM y hy0 s hs (hInv s hs)
  choose! κs xs hks using hlev
  set K₁ := ∑ s ∈ Finset.range e, κs s with hK₁
  set x' : ℕ → O := fun s => ((PD.p : ℕ) : O) ^ (K₁ - κs s) * xs s with hx'
  have hum : ∀ s < e, u s ∈ W.AΔ := fun s hs => by
    rw [hus s hs]
    exact W.AΔ.mul_mem (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W)
      (W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem (hps t) _)) (hrs s hs)
  set Y' := lE W (κc + K₁) * PPγ W e JS y - ∑ s ∈ Finset.range e, x' s • ιE (letE a * u s) with hY'
  have hPPm : InId W a e α0 (PPγ W e JS y) := inId_aeval W hS _ y hy0
  have hY'm : InId W a e α0 Y' :=
    inId_sub W (inId_lE W hPPm _) (inId_sum W _ _ fun s hs =>
      inId_smul W (inId0_of_mem W H a e (hum s (Finset.mem_range.1 hs))) _)
  obtain ⟨z', hz'm, hz'⟩ := (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A a e Y').2 hY'm
  obtain ⟨o', w', hw'm, hval⟩ := value0 W hR a z' hz'm
  set C0 := ιE (letE a * (Λ * r₀)) with hC0
  have hC0m : InId W a e α0 C0 := inId0_of_mem W H a e (W.AΔ.mul_mem hΛm hr₀)
  set Y := lE W κc * Y' - o' • C0 with hYdef
  have hYm : InId W a e α0 Y := inId_sub W (inId_lE W hY'm _) (inId_smul W hC0m _)
  have hYΛ : InFr W a 1 Λ Y := (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A a e Y).2 hYm

  have hlevel : ∀ s < e, InId W a e (Function.update α0 s (H s)) Y := by
    intro s hs
    have hsm : s ∈ Finset.range e := Finset.mem_range.2 hs
    have hdvu : ∀ t ∈ (Finset.range e).erase s, Dv W H s (u t) := by
      intro t ht
      obtain ⟨hts, htm⟩ := Finset.mem_erase.1 ht
      rw [hus t (Finset.mem_range.1 htm)]
      have := dv_prod W H 2 (by norm_num) ((Finset.range e).erase t) s
        (Finset.mem_erase.2 ⟨Ne.symm hts, hsm⟩) (hrs t (Finset.mem_range.1 htm))
      obtain ⟨r, hr, he⟩ := this
      exact ⟨W.π₀ * r, W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) hr, by rw [mul_assoc, he]; ring⟩
    have hdv0 : Dv W H s (lA W ^ κc - u s) := by
      have e1 : lA W ^ κc - u s = u₀ + ∑ t ∈ (Finset.range e).erase s, u t := by
        rw [hsum, ← Finset.add_sum_erase _ _ hsm]; ring
      rw [e1, hu₀]
      exact dv_add W (dv_prod W H 2 (by norm_num) _ s hsm hr₀) (dv_sum W _ _ hdvu)
    have hdvΛ : Dv W H s (Λ * r₀) := by
      have := dv_prod W H 1 le_rfl (Finset.range e) s hsm hr₀
      simpa [hΛ, abelian₂] using this
    have hdec : Y = lE W κc * (lE W κc * (lE W (K₁ - κs s) *
          (lE W (κs s) * PPγ W e JS y - ιE (letE a) * algebraMap O W.EE (xs s)))) +
        lE W κc * (x' s • ιE (letE a * (lA W ^ κc - u s))) -
        lE W κc * ∑ t ∈ (Finset.range e).erase s, x' t • ιE (letE a * u t) - o' • C0 := by
      have hK : κc + K₁ = κc + (K₁ - κs s) + κs s := by
        have : κs s ≤ K₁ := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hsm
        omega
      rw [hYdef, hY', ← Finset.add_sum_erase _ _ hsm, hK, lE_add', lE_add', hx']
      simp only [lE, lA, Algebra.smul_def, map_mul, map_sub, map_pow, map_natCast]
      ring
    rw [hdec]
    refine inId_sub W (inId_sub W (inId_add W ?_ ?_) ?_) ?_
    · exact inId_lE W (inId_lE W (inId_lE W (hks s hs) _) _) _
    · obtain ⟨r, hr, he⟩ := hdv0
      exact inId_lE W (inId_smul W (piece_upd W H a e s hs _ r hr he) _) _
    · refine inId_lE W (inId_sum W _ _ fun t ht => inId_smul W ?_ _) _
      obtain ⟨r, hr, he⟩ := hdvu t ht
      exact piece_upd W H a e s hs _ r hr he
    · obtain ⟨r, hr, he⟩ := hdvΛ
      exact inId_smul W (piece_upd W H a e s hs _ r hr he) _

  have hV : ∑ s ∈ Finset.range e, u s = W.π₀ *
      ∑ s ∈ Finset.range e, (∏ t ∈ (Finset.range e).erase s, ps W t ^ (2 * H t)) * rs s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hus s (Finset.mem_range.1 hs)]; ring
  have hΛ2 : Λ * (Λ * r₀) = u₀ := by
    rw [hu₀, ← mul_assoc, ← sq, hΛ, abelian₂, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [← pow_mul, mul_comm]
  have hπ : InFr W a W.π₀ Λ Y := by
    refine ⟨lA W ^ κc * w' + algebraMap O (LetA O n) o' *
        ∑ s ∈ Finset.range e, (∏ t ∈ (Finset.range e).erase s, ps W t ^ (2 * H t)) * rs s,
      W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.KL.lA_mem W) _) hw'm)
        (W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.sum_mem fun s hs =>
          W.AΔ.mul_mem (W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem (hps t) _)
            (hrs s (Finset.mem_range.1 hs)))), ?_⟩
    have hE : ιE Λ * Y = ιE (lA W ^ κc * (letE a * 1 * z') -
        algebraMap O (LetA O n) o' * (letE a * (Λ * (Λ * r₀)))) := by
      have h1 : ιE Λ * Y = lE W κc * (ιE Λ * Y') - algebraMap O W.EE o' * (ιE Λ * C0) := by
        rw [hYdef, Algebra.smul_def]; ring
      rw [h1, hz', hC0, ← Formalism.MainNotions.UnusedSlot80.KL.ι_lE W κc, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
      simp only [← map_mul, ← map_sub]
      congr 1
      ring
    rw [hE]
    congr 1
    linear_combination (lA W ^ κc) * hval - (algebraMap O (LetA O n) o' * letE a) * hΛ2 +
      (algebraMap O (LetA O n) o' * letE a) * hsum + (algebraMap O (LetA O n) o' * letE a) * hV

  obtain ⟨f₁, f₂, hYf, hf₁, hf₂⟩ := hRAT hCA h5 A a e 1 (fun s => ((H s : ℕ) : ℤ)) le_rfl
    (fun s _ => ⟨by omega, le_rfl⟩) Y hYΛ
    (fun s hs => ⟨0, Y, 0, by simp [lE], by
      have := hlevel s hs
      unfold InId at this
      have en := numI_upd W H e s hs (H s)
      have ed := denI_upd W H e s hs (H s)
      simp only [numI, denI] at en ed
      rw [en, ed] at this
      exact this, ⟨0, W.AΔ.zero_mem, by simp⟩⟩)
    (fun _ => ⟨0, Y, 0, by simp [lE], hπ, ⟨0, W.AΔ.zero_mem, by simp⟩⟩)
  have hf₁' : InFr W a (W.π₀ * Λ) 1 f₁ := by
    have h1 : (∏ s ∈ Finset.range e, ps W s ^ (-((H s : ℕ) : ℤ)).toNat) = 1 :=
      Finset.prod_eq_one fun s _ => by rw [show (-((H s : ℕ) : ℤ)).toNat = 0 by omega, pow_zero]
    have h2 : (∏ s ∈ Finset.range e, ps W s ^ (((H s : ℕ) : ℤ)).toNat) = Λ := by
      rw [hΛ, abelian₂]; exact Finset.prod_congr rfl fun s _ => by rw [Int.toNat_natCast]
    rw [h1, h2, pow_one] at hf₁
    exact hf₁
  refine ⟨κc + (κc + K₁), fun s => ((PD.p : ℕ) : O) ^ κc * x' s, o', ?_⟩
  have hfin : lE W (κc + (κc + K₁)) * PPγ W e JS y -
      ∑ s ∈ Finset.range e, (((PD.p : ℕ) : O) ^ κc * x' s) • ιE (letE a * u s) -
        o' • ιE (letE a * (Λ * r₀)) = f₁ + f₂ := by
    rw [← hYf, hYdef, hY', hC0, lE_add']
    simp only [lE, Algebra.smul_def, map_mul, map_pow, map_natCast, Finset.mul_sum, mul_sub, mul_assoc]
  rw [hfin]
  obtain ⟨u₁, hu₁, e₁⟩ := hf₁'
  obtain ⟨u₂, hu₂, e₂⟩ := hf₂
  exact ⟨u₁ + u₂, W.AΔ.add_mem hu₁ hu₂, by rw [mul_add, e₁, e₂, ← map_add]; congr 1; ring⟩

end Formalism.MainNotions.UnusedSlot80.UGen
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE
local notation "aev" => Polynomial.aeval (AlgHom.toLinearMap (W.γE W.gam) : Module.End O W.EE)

theorem uniformizer_isUnit_etale (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : IsUnit (ιE W.π₀) := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  rw [hw, map_mul, map_pow]
  exact (w.isUnit.map _).mul (W.EE_π.pow _)

def πinv (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : W.EE := (((uniformizer_isUnit_etale W hR).unit⁻¹ : W.EEˣ) : W.EE)

theorem πinv_mul (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : πinv W hR * ιE W.π₀ = 1 := by
  unfold πinv
  nth_rewrite 2 [← (uniformizer_isUnit_etale W hR).unit_spec]
  exact Units.inv_mul _

theorem nl_of_pi0Lam (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) [IsDomain O]
    (hbij : Function.Bijective (algebraMap K₀ K)) (A : ArcP n) (hA : A.OK) (c : ZMod n)
    (hc : c ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T (c - ((A.len c : ℕ) : ZMod n)) b) (f : Fin d → W.EE)
    (hf : ∀ k, InFr W c (W.π₀ * abelian₂ W A c (A.len c)) 1 (f k)) :
    ∃ g, InNL W T c (A.len c) (abelian₂ W A c (A.len c)) b g ∧ ∀ k, f k = ιE W.π₀ * g k := by
  set e := A.len c with he
  set Λ := abelian₂ W A c e with hΛ
  have hc' : c - ((e : ℕ) : ZMod n) ∈ A.cuts := ((hA.2.2.1 c hc).2.2).1
  have hce : c - ((e : ℕ) : ZMod n) + ((e : ℕ) : ZMod n) = c := sub_add_cancel _ _
  set g : Fin d → W.EE := fun k => πinv W hR * f k with hg
  have hfg : ∀ k, f k = ιE W.π₀ * g k := fun k => by
    rw [hg, ← mul_assoc, mul_comm (ιE W.π₀), πinv_mul, one_mul]
  have hgu : ∀ k, ∃ u ∈ W.AΔ, g k = ιE (letE c * Λ * u) := by
    intro k
    obtain ⟨u, hu, hfu⟩ := hf k
    refine ⟨u, hu, ?_⟩
    rw [map_one, one_mul] at hfu
    show πinv W hR * f k = _
    rw [hfu]
    simp only [map_mul]
    have := πinv_mul W hR
    linear_combination (ιE (letE c) * ιE Λ * ιE u) * this
  refine ⟨g, ⟨fun k => ?_, 0, ?_⟩, hfg⟩
  · obtain ⟨u, hu, hgk⟩ := hgu k
    have hΛm : Λ ∈ W.AΔ := W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem
      (Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) t) _
    refine ⟨Λ * Λ * u, W.AΔ.mul_mem (W.AΔ.mul_mem hΛm hΛm) hu, ?_⟩
    rw [hgk, ← map_mul]; congr 1; ring
  · refine ⟨d, g, fun i => Pi.single i 1, fun _ s => ((A.Hs c e s : ℕ) : ℤ), fun i => ⟨?_, ?_⟩, fun k => ?_⟩
    · obtain ⟨u, hu, hgk⟩ := hgu i
      unfold InId
      have h1 : (∏ s ∈ Finset.range e, ps W s ^ (-((A.Hs c e s : ℕ) : ℤ)).toNat) = 1 :=
        Finset.prod_eq_one fun s _ => by rw [show (-((A.Hs c e s : ℕ) : ℤ)).toNat = 0 by omega, pow_zero]
      have h2 : (∏ s ∈ Finset.range e, ps W s ^ (((A.Hs c e s : ℕ) : ℤ)).toNat) = Λ := by
        rw [hΛ, abelian₂]; exact Finset.prod_congr rfl fun s _ => by rw [Int.toNat_natCast]
      rw [h1, h2]
      exact ⟨u, hu, by rw [map_one, one_mul, hgk]⟩
    · intro s hs
      have := Formalism.MainNotions.UnusedSlot80.LevC.dvO_filLow W hbij A hA _ hc' T hT b hb e s hs (Pi.single i 1)
      rw [hce] at this
      exact this
    · simp only [lE, pow_zero, one_mul]
      rw [Finset.sum_eq_single k]
      · simp
      · intro i _ hik; simp [Pi.single_apply, Ne.symm hik]
      · simp

variable [IsDomain O]

include W in
theorem p_ne_zero_O' : ((PD.p : ℕ) : O) ≠ 0 := by
  intro h
  have h1 : ((PD.p : ℕ) : LL) = 0 := by rw [← map_natCast (algebraMap O LL), h, map_zero]
  have h2 := W.v_l
  rw [h1, AddValuation.map_zero] at h2
  exact absurd h2 (by simp)

theorem uniformizer_dvd_of_prime_power (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (a : ZMod n) {u v : LetA O n}
    (hu : u ∈ W.AΔ) (K : ℕ) (h : lA W ^ K * (letE a * u) = W.π₀ * (letE a * v)) :
    ∃ w ∈ W.AΔ, (letE a : LetA O n) * u = W.π₀ * (letE a * w) := by
  obtain ⟨o, w, hw, hval⟩ := value0 W hR a u hu
  have hrel : lA W ^ K * (letE a * algebraMap O (LetA O n) o) =
      W.π₀ * (letE a * v - lA W ^ K * (letE a * w)) := by
    rw [mul_sub, ← h, hval]; ring
  have h1 := congrArg (fun z : LetA O n => PowerSeries.constantCoeff (z a)) hrel
  simp only [Pi.mul_apply, Pi.pow_apply, lA, Pi.natCast_apply, letE, Pi.single_eq_same, one_mul,
    Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply, PowerSeries.smul_eq_C_mul, mul_one,
    map_mul, map_pow, map_natCast, PowerSeries.constantCoeff_C, LocWach.π₀,
    Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR, zero_mul] at h1
  have ho : o = 0 := by
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (pow_ne_zero K (p_ne_zero_O' W))
    · exact h2
  refine ⟨w, hw, ?_⟩
  rw [hval, ho, map_zero, zero_add]; ring

theorem sat_l (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (T : LocLat G Qp LL O) (A : ArcP n) (c : ZMod n)
    (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (K : ℕ) (f : Fin d → W.EE)
    (hf : ∀ k, InFr W c 1 (abelian₂ W A c e) (f k)) (g : Fin d → W.EE)
    (hg : InNL W T c e (abelian₂ W A c e) b g) (hfg : ∀ k, lE W K * f k = ιE W.π₀ * g k) :
    ∃ g', InNL W T c e (abelian₂ W A c e) b g' ∧ ∀ k, f k = ιE W.π₀ * g' k := by
  set Λ := abelian₂ W A c e with hΛ
  set g' : Fin d → W.EE := fun k => πinv W hR * f k with hg'
  have hfg' : ∀ k, f k = ιE W.π₀ * g' k := fun k => by
    rw [hg', ← mul_assoc, mul_comm (ιE W.π₀), πinv_mul, one_mul]
  have hcoef : ∀ k, InFr W c 1 Λ (g' k) := by
    intro k
    obtain ⟨u, hu, hfu⟩ := hf k
    obtain ⟨v', hv', hgv⟩ := hg.1 k
    have hrel : lA W ^ K * (letE c * u) = W.π₀ * (letE c * v') := by
      apply W.EE_inj
      have e1 := hfu; have e2 := hgv
      rw [mul_one] at e1 e2
      calc ιE (lA W ^ K * (letE c * u)) = lE W K * (ιE Λ * f k) := by
            rw [map_mul, ← e1, Formalism.MainNotions.UnusedSlot80.KL.ι_lE]
        _ = ιE Λ * (lE W K * f k) := by ring
        _ = ιE Λ * (ιE W.π₀ * g k) := by rw [hfg k]
        _ = ιE W.π₀ * (ιE Λ * g k) := by ring
        _ = ιE (W.π₀ * (letE c * v')) := by rw [e2]; simp only [map_mul]
    obtain ⟨w, hw, hwe⟩ := uniformizer_dvd_of_prime_power W hR c hu K hrel
    refine ⟨w, hw, ?_⟩
    show ιE Λ * (πinv W hR * f k) = ιE (letE c * 1 * w)
    rw [mul_left_comm, hfu]
    try simp only [mul_one]
    rw [hwe, map_mul, ← mul_assoc, πinv_mul, one_mul]
  obtain ⟨κ, hs⟩ := hg.2
  refine ⟨g', ⟨hcoef, κ + K, ?_⟩, hfg'⟩
  convert hs using 1
  funext k
  show lE W (κ + K) * (πinv W hR * f k) = lE W κ * g k
  rw [lE_add']
  linear_combination (lE W κ * πinv W hR) * hfg k + (lE W κ * g k) * πinv_mul W hR

theorem eval_one_dvd_prime_pow (hKL : KillerLevCore W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (ell : ℕ) (JS : Finset ℤ) :
    ∃ (N : ℕ) (o : O), o * (PPO W ell JS).eval 1 = ((PD.p : ℕ) : O) ^ N := by
  obtain ⟨hv, -⟩ := hKL hCA ell JS
  set N := ell + ∑ i ∈ JS.erase 0, (ell + 1 + padicValInt PD.p i) with hN
  set z := algebraMap O LL ((PPO W ell JS).eval 1) with hz
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hv
    exact WithTop.top_ne_coe hv
  have hx : v (((PD.p : ℕ) : LL) ^ N * z⁻¹) = 0 := by
    rw [AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_inv, hv]
    have hl : v ((PD.p : ℕ) : LL) = 1 := W.v_l
    rw [hl]
    have : (N • (1 : WithTop ℚ)) = ((N : ℚ) : WithTop ℚ) := by simp
    rw [this]
    have : ((N : ℕ) : WithTop ℚ) = ((N : ℚ) : WithTop ℚ) := by simp
    rw [this, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, add_neg_cancel]
    rfl
  obtain ⟨o, ho⟩ := hO2 _ (le_of_eq hx.symm)
  refine ⟨N, o, hinj ?_⟩
  rw [map_mul, ho, ← hz, map_pow, map_natCast, mul_assoc, inv_mul_cancel₀ hz0, mul_one]

theorem exists_gammaA_pi0_eq_pi0_mul_of_RingP (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.2.2.1
  rw [Formalism.MainNotions.UnusedSlot80.ToolsR.eat_qP] at hw
  have hwq : (w : LetA O n) * Formalism.MainNotions.WachCoordinates.qP W ∈ W.AΔ := by
    refine Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ hR.1 (fun i => Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_ne hR) ?_
    have e : W.π₀ * ((w : LetA O n) * Formalism.MainNotions.WachCoordinates.qP W) = W.γA W.gam W.π₀ - W.π₀ := by rw [hw]; ring
    rw [e]
    exact W.AΔ.sub_mem (Formalism.MainNotions.UnusedSlot80.KL.γA_mem W W.gam hR.1) hR.1
  exact ⟨1 + (w : LetA O n) * Formalism.MainNotions.WachCoordinates.qP W, W.AΔ.add_mem W.AΔ.one_mem hwq, by
    linear_combination hw⟩

theorem lattice_membership_aeval_uniformizer (hS : PsStable W) (hP : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (T : LocLat G Qp LL O) (A : ArcP n) (a : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (P : Polynomial O) : ∀ g : Fin d → W.EE, InNL W T a e (abelian₂ W A a e) b g →
      ∃ g' : Fin d → W.EE, InNL W T a e (abelian₂ W A a e) b g' ∧
        ∀ k, aev P (ιE W.π₀ * g k) = ιE W.π₀ * g' k := by
  induction P using Polynomial.induction_on with
  | C c =>
    intro g hg
    refine ⟨fun k => c • g k, Formalism.MainNotions.UnusedSlot80.UnivC.inNL_smul W T A a e b c hg, fun k => ?_⟩
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact (mul_smul_comm c (ιE W.π₀) (g k)).symm
  | add p q hp hq =>
    intro g hg
    obtain ⟨g₁, h₁, e₁⟩ := hp g hg
    obtain ⟨g₂, h₂, e₂⟩ := hq g hg
    refine ⟨g₁ + g₂, Formalism.MainNotions.UnusedSlot80.UnivC.inNL_add W T A a e b h₁ h₂, fun k => ?_⟩
    simp only [map_add, LinearMap.add_apply, e₁, e₂, Pi.add_apply, mul_add]
  | monomial k c ih =>
    intro g hg
    obtain ⟨u, hu, hγ⟩ := hP
    have hx : ∀ k', (AlgHom.toLinearMap (W.γE W.gam) : Module.End O W.EE) (ιE W.π₀ * g k') =
        ιE W.π₀ * (ιE u * W.γE W.gam (g k')) := by
      intro k'
      rw [AlgHom.toLinearMap_apply, map_mul, W.γE_ext]
      show ιE (W.γA W.gam W.π₀) * _ = _
      rw [hγ, map_mul]
      ring
    obtain ⟨g', hg', e'⟩ := ih (fun k' => ιE u * W.γE W.gam (g k'))
      (Formalism.MainNotions.UnusedSlot80.UnivC.inNL_mulι W T A a e b hu (Formalism.MainNotions.UnusedSlot80.UnivC.inNL_γ W T A a e b hS hg))
    refine ⟨g', hg', fun k' => ?_⟩
    rw [pow_succ, ← mul_assoc, Polynomial.aeval_mul, Module.End.mul_apply, Polynomial.aeval_X, hx, e']

theorem pp_inv (hS : PsStable W) (hP : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (T : LocLat G Qp LL O) (A : ArcP n) (a : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (P : Polynomial O) (f : Fin d → W.EE) (hf : InvNL W T a e (abelian₂ W A a e) b f) :
    ∃ g, InNL W T a e (abelian₂ W A a e) b g ∧ ∀ k, aev P (f k) - P.eval 1 • f k = ιE W.π₀ * g k := by
  obtain ⟨g, hg, hfg⟩ := hf
  set p' : Polynomial O := P - Polynomial.C (P.eval 1) with hp'
  have hroot : p'.IsRoot 1 := by simp [hp']
  set S := p' /ₘ (Polynomial.X - Polynomial.C 1) with hSdef
  have hS' : (Polynomial.X - Polynomial.C 1) * S = p' := (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hroot
  obtain ⟨g', hg', e'⟩ := lattice_membership_aeval_uniformizer W hS hP T A a e b S g hg
  refine ⟨g', hg', fun k => ?_⟩
  have h1 : aev P (f k) - P.eval 1 • f k = aev p' (f k) := by
    rw [hp', map_sub, LinearMap.sub_apply, Polynomial.aeval_C, Module.algebraMap_end_apply]
  rw [h1, ← hS', mul_comm, map_mul, Module.End.mul_apply, map_sub, LinearMap.sub_apply,
    Polynomial.aeval_X, Polynomial.aeval_C, map_one, Module.End.one_apply, AlgHom.toLinearMap_apply,
    hfg k, e' k]

end Formalism.MainNotions.UnusedSlot80.UGen
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE

section Mod

variable (T : LocLat G Qp LL O) (A : ArcP n) (c : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
  (Rst : Finset (Fin d))

theorem inFr1_add {f g : W.EE} (hf : InFr W c 1 (abelian₂ W A c e) f) (hg : InFr W c 1 (abelian₂ W A c e) g) :
    InFr W c 1 (abelian₂ W A c e) (f + g) :=
  (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).2 (inId_add W
    ((Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).1 hf) ((Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).1 hg))

theorem inFr1_smul (o : O) {f : W.EE} (hf : InFr W c 1 (abelian₂ W A c e) f) :
    InFr W c 1 (abelian₂ W A c e) (o • f) :=
  (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).2 (inId_smul W
    ((Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).1 hf) o)

theorem inFr1_zero : InFr W c 1 (abelian₂ W A c e) 0 := ⟨0, W.AΔ.zero_mem, by simp⟩

def Msub : Submodule O (Fin d → W.EE) where
  carrier := {f | (∀ k, InFr W c 1 (abelian₂ W A c e) (f k)) ∧ ∀ k ∉ Rst, f k = 0}
  add_mem' := fun {f g} hf hg => ⟨fun k => inFr1_add W A c e (hf.1 k) (hg.1 k),
    fun k hk => by simp [hf.2 k hk, hg.2 k hk]⟩
  zero_mem' := ⟨fun _ => inFr1_zero W A c e, fun _ _ => rfl⟩
  smul_mem' := fun o f hf => ⟨fun k => inFr1_smul W A c e o (hf.1 k), fun k hk => by simp [hf.2 k hk]⟩

def Psub : Submodule O (Fin d → W.EE) where
  carrier := {f | f ∈ Msub W A c e Rst ∧
    ∃ g, InNL W T c e (abelian₂ W A c e) b g ∧ ∀ k, f k = ιE W.π₀ * g k}
  add_mem' := by
    rintro f f' ⟨hf, g, hg, hfg⟩ ⟨hf', g', hg', hfg'⟩
    exact ⟨(Msub W A c e Rst).add_mem hf hf', g + g',
      Formalism.MainNotions.UnusedSlot80.UnivC.inNL_add W T A c e b hg hg', fun k => by simp [hfg k, hfg' k, mul_add]⟩
  zero_mem' := ⟨(Msub W A c e Rst).zero_mem, 0, Formalism.MainNotions.UnusedSlot80.UnivC.inNL_zero W T A c e b,
    fun k => by simp⟩
  smul_mem' := by
    rintro o f ⟨hf, g, hg, hfg⟩
    exact ⟨(Msub W A c e Rst).smul_mem o hf, fun k => o • g k,
      Formalism.MainNotions.UnusedSlot80.UnivC.inNL_smul W T A c e b o hg, fun k => by
        rw [Pi.smul_apply, hfg k, mul_smul_comm]⟩

def Isub : Submodule O (Fin d → W.EE) where
  carrier := {f | f ∈ Msub W A c e Rst ∧ InvNL W T c e (abelian₂ W A c e) b f}
  add_mem' := by
    rintro f f' ⟨hf, g, hg, hfg⟩ ⟨hf', g', hg', hfg'⟩
    refine ⟨(Msub W A c e Rst).add_mem hf hf', g + g',
      Formalism.MainNotions.UnusedSlot80.UnivC.inNL_add W T A c e b hg hg', fun k => ?_⟩
    simp only [Pi.add_apply, map_add]
    rw [mul_add, ← hfg k, ← hfg' k]; ring
  zero_mem' := ⟨(Msub W A c e Rst).zero_mem, 0, Formalism.MainNotions.UnusedSlot80.UnivC.inNL_zero W T A c e b,
    fun k => by simp⟩
  smul_mem' := by
    rintro o f ⟨hf, g, hg, hfg⟩
    refine ⟨(Msub W A c e Rst).smul_mem o hf, fun k => o • g k,
      Formalism.MainNotions.UnusedSlot80.UnivC.inNL_smul W T A c e b o hg, fun k => ?_⟩
    simp only [Pi.smul_apply, map_smul]
    rw [← smul_sub, hfg k, mul_smul_comm]

theorem inFr1_of_pi0Lam {f : W.EE} (hf : InFr W c (W.π₀ * abelian₂ W A c e) 1 f) :
    InFr W c 1 (abelian₂ W A c e) f := by
  obtain ⟨w, hw, hfw⟩ := hf
  have hΛm : abelian₂ W A c e ∈ W.AΔ := W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem
    (Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) t) _
  refine ⟨abelian₂ W A c e * (W.π₀ * abelian₂ W A c e) * w,
    W.AΔ.mul_mem (W.AΔ.mul_mem hΛm (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) hΛm)) hw, ?_⟩
  rw [map_one, one_mul] at hfw
  rw [hfw, ← map_mul]; congr 1; ring

theorem psub_of_pi0Lam [IsDomain O] (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hbij : Function.Bijective (algebraMap K₀ K)) (hA : A.OK) (hc : c ∈ A.cuts) (hT : Win W A T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T (c - ((A.len c : ℕ) : ZMod n)) b) (f : Fin d → W.EE)
    (hf : ∀ k, InFr W c (W.π₀ * abelian₂ W A c (A.len c)) 1 (f k)) (hs : ∀ k ∉ Rst, f k = 0) :
    f ∈ Psub W T A c (A.len c) b Rst := by
  obtain ⟨g, hg, hfg⟩ := nl_of_pi0Lam W hR hbij A hA c hc T hT b hb f hf
  exact ⟨⟨fun k => inFr1_of_pi0Lam W A c _ (hf k), hs⟩, g, hg, hfg⟩

end Mod

end Formalism.MainNotions.UnusedSlot80.UGen
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE
local notation "aev" => Polynomial.aeval (AlgHom.toLinearMap (W.γE W.gam) : Module.End O W.EE)

theorem single_mem_span {d : ℕ} {ι : Type} [Fintype ι] (V : ι → Fin d → W.EE) (k : Fin d) (x : W.EE)
    (i : ι) (hV : V i = Pi.single k x) : Pi.single k x ∈ Submodule.span O (Set.range fun j : Fin (Fintype.card ι) =>
      V ((Fintype.equivFin ι).symm j)) := by
  refine Submodule.subset_span ⟨Fintype.equivFin ι i, ?_⟩
  simp [hV]

theorem univGenCore_of' [IsDomain O] [IsPrincipalIdealRing O] [NeZero n]
    [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] [Fintype (K →ₐ[Qp] LL)]
    (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O))
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hKL : KillerLevCore W) (hS : PsStable W)
    (hRAT : CutU.RATCore W)
    (hInv : ∀ (A : ArcP n) (c : ZMod n), c ∈ A.cuts → ∀ s < A.len c, InvLevAt W s)
    (hFin : FinLev W) : Formalism.MainNotions.UnusedSlot80.UnivC.UnivGenCore PD W := by
  intro A m T₂ c hsit d b sol Rst hFO
  obtain ⟨hCA, h5, hAOK, hWin, -, hc⟩ := hsit
  have hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T₂ (c - ((A.len c : ℕ) : ZMod n)) b := hFO.1.1
  have hbij := hCA.1
  set e := A.len c with he
  set Λ := abelian₂ W A c e with hΛ
  set H : ℕ → ℕ := A.Hs c e with hH
  set M := ∑ s ∈ Finset.range e, H s with hMdef
  have hM : ∀ s < e, A.Hs c e s ≤ M := fun s hs =>
    Finset.single_le_sum (f := H) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
  set JS : Finset ℤ := Finset.Ico (-(M : ℤ)) M with hJS
  set t : O := (PPO W e JS).eval 1 with ht
  set lR : O := ((PD.p : ℕ) : O) with hlR
  have hps := Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W)
  have hΛm : Λ ∈ W.AΔ := W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (hps s) _

  obtain ⟨κc, u₀, hu₀m, u, hum, hsum, ⟨r₀, hr₀, hu₀⟩, hus⟩ :=
    Formalism.MainNotions.UnusedSlot80.LevC.crtLev W hR e (fun t => 2 * H t)
  choose! rs hrs hus' using hus

  have hp0 := p_ne_zero_O' W
  have hU : PsUnitE W := Formalism.MainNotions.UnusedSlot80.KF.psUnitE_of W hR
    ⟨Formalism.MainNotions.UnusedSlot80.ToolsR.tools1 hR, Formalism.MainNotions.UnusedSlot80.ToolsR.tools2 hR hp0 hpu,
      Formalism.MainNotions.UnusedSlot80.ToolsR.tools3 hR, Formalism.MainNotions.UnusedSlot80.ToolsR.tools4 hR⟩
  have hΛU : IsUnit (ιE Λ) := by
    refine ⟨∏ s ∈ Finset.range e, (hU s).unit ^ H s, ?_⟩
    rw [Units.coe_prod, hΛ, abelian₂, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, map_pow]
  set Λi : W.EE := ((hΛU.unit⁻¹ : W.EEˣ) : W.EE) with hΛi
  have hΛinv : Λi * ιE Λ = 1 := by
    rw [hΛi]; nth_rewrite 2 [← hΛU.unit_spec]; exact Units.inv_mul _
  have hP := exists_gammaA_pi0_eq_pi0_mul_of_RingP W hR

  set Ms := Msub W A c e Rst with hMs
  set Ps := Psub W T₂ A c e b Rst with hPs
  set Is := Isub W T₂ A c e b Rst with hIs
  have hIM : Is ≤ Ms := fun f hf => hf.1

  obtain ⟨D, hD⟩ := hFin c e H
  set F : Fin d × Fin D → Fin d → W.EE := fun p => Pi.single p.1 (Λi * ιE (letE c * W.π₀ ^ (p.2 : ℕ)))
    with hF
  have hfg : Ms ≤ Submodule.span O (Set.range F) ⊔ Ps := by
    intro f hf
    have hdec : ∀ k, ∃ (cc : Fin D → O) (R : W.EE), InFr W c (W.π₀ * Λ) 1 R ∧ (k ∉ Rst → R = 0) ∧
        f k = ∑ j, cc j • (Λi * ιE (letE c * W.π₀ ^ (j : ℕ))) + R := by
      intro k
      by_cases hk : k ∈ Rst
      · obtain ⟨uu, huu, hfu⟩ := hf.1 k
        obtain ⟨cc, w, hw, hcw⟩ := hD uu huu
        rw [show (∏ t ∈ Finset.range e, ps W t ^ H t) = Λ from rfl] at hcw
        refine ⟨cc, ιE (letE c * (W.π₀ * Λ) * w), ⟨w, hw, by rw [map_one, one_mul]⟩,
          fun h => absurd hk h, ?_⟩
        have hsm : ∑ j, cc j • (Λi * ιE (letE c * W.π₀ ^ (j : ℕ))) =
            Λi * ιE (letE c * ∑ j : Fin D, algebraMap O (LetA O n) (cc j) * W.π₀ ^ (j : ℕ)) := by
          rw [Finset.mul_sum, map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
          simp only [map_mul]; ring
        have hfk : ιE Λ * f k = ιE (letE c * ∑ j : Fin D, algebraMap O (LetA O n) (cc j) * W.π₀ ^ (j : ℕ)) +
            ιE Λ * ιE (letE c * (W.π₀ * Λ) * w) := by
          rw [hfu, mul_one, hcw, map_add, ← map_mul]; congr 1; congr 1; ring
        rw [hsm]
        linear_combination Λi * hfk - (f k - ιE (letE c * (W.π₀ * Λ) * w)) * hΛinv
      · exact ⟨0, 0, ⟨0, W.AΔ.zero_mem, by simp⟩, fun _ => rfl, by simp [hf.2 k hk]⟩
    choose cc R hR1 hR2 hR3 using hdec
    have hRv : (fun k => R k) ∈ Ps :=
      psub_of_pi0Lam W T₂ A c b Rst hR hbij hAOK hc hWin hb _ hR1 fun k hk => hR2 k hk
    have hfeq : f = ∑ p : Fin d × Fin D, cc p.1 p.2 • F p + fun k => R k := by
      funext k
      rw [hR3 k, Pi.add_apply, Finset.sum_apply, Fintype.sum_prod_type]
      simp only [Pi.smul_apply, hF, Pi.single_apply]
      rw [Finset.sum_eq_single k]
      · simp
      · intro k' _ hk'; simp [Ne.symm hk']
      · simp
    rw [hfeq]
    exact Submodule.add_mem_sup (Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)) hRv

  set Cg : ℕ → W.EE := fun j => if j < e then ιE (letE c * u j) else ιE (letE c * (Λ * r₀)) with hCg
  set ιv := {k // k ∈ Rst} × Fin (e + 1)
  set vv : ιv → Fin d → W.EE := fun p => Pi.single p.1.1 (Cg p.2) with hvv
  set v' : Fin (Fintype.card ιv) → Fin d → W.EE := fun j => vv ((Fintype.equivFin ιv).symm j) with hv'
  have hvmem : ∀ k ∈ Rst, ∀ j < e + 1, Pi.single k (Cg j) ∈ Submodule.span O (Set.range v') :=
    fun k hk j hj => single_mem_span W vv k _ (⟨k, hk⟩, ⟨j, hj⟩) rfl

  have hK : ∀ f ∈ Is, ∃ K : ℕ, (lR ^ K * t) • f ∈ Submodule.span O (Set.range v') ⊔ Ps := by
    intro f hf
    obtain ⟨g₁, hg₁, hpp⟩ := pp_inv W hS hP T₂ A c e b (PPO W e JS) f hf.2
    have hke := fun k => killer_elem W hR hKL hS hRAT hCA h5 A c e M hM (hInv A c hc) κc u₀ r₀ u rs hr₀
      (fun s hs => hrs s hs) hsum hu₀ (fun s hs => hus' s hs) (f k) (hf.1.1 k)
    choose Kk xk x0k hRk using hke
    set Kt := ∑ k, Kk k with hKt
    have hKle : ∀ k, Kk k ≤ Kt := fun k => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    set Sv : Fin d → W.EE := ∑ k ∈ Rst, (∑ s ∈ Finset.range e,
        (lR ^ (Kt - Kk k) * xk k s) • (Pi.single k (Cg s) : Fin d → W.EE) +
          (lR ^ (Kt - Kk k) * x0k k) • (Pi.single k (Cg e) : Fin d → W.EE))
      with hSv
    set Rr : Fin d → W.EE := fun k => if k ∈ Rst then lE W (Kt - Kk k) *
        (lE W (Kk k) * PPγ W e JS (f k) - ∑ s ∈ Finset.range e, xk k s • ιE (letE c * u s) -
          x0k k • ιE (letE c * (Λ * r₀))) else 0 with hRr
    set D2 : Fin d → W.EE := fun k => lE W Kt * (ιE W.π₀ * g₁ k) with hD2
    have hSvm : Sv ∈ Submodule.span O (Set.range v') := by
      refine Submodule.sum_mem _ fun k hk => Submodule.add_mem _ (Submodule.sum_mem _ fun s hs => ?_) ?_
      · exact Submodule.smul_mem _ _ (hvmem k hk s (by have := Finset.mem_range.1 hs; omega))
      · exact Submodule.smul_mem _ _ (hvmem k hk e (by omega))
    have hRrm : Rr ∈ Ps := by
      refine psub_of_pi0Lam W T₂ A c b Rst hR hbij hAOK hc hWin hb _ (fun k => ?_) (fun k hk => by simp [hRr, hk])
      by_cases hk : k ∈ Rst
      · simp only [hRr, hk, if_true]
        obtain ⟨w, hw, hwe⟩ := hRk k
        refine ⟨lA W ^ (Kt - Kk k) * w, W.AΔ.mul_mem (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.KL.lA_mem W) _) hw, ?_⟩
        rw [map_one, one_mul] at hwe ⊢
        rw [hwe, ← Formalism.MainNotions.UnusedSlot80.KL.ι_lE, ← map_mul]; congr 1; ring
      · simp only [hRr, hk, if_false]; exact ⟨0, W.AΔ.zero_mem, by simp⟩
    have hf0 : ∀ k ∉ Rst, ιE W.π₀ * g₁ k = 0 := fun k hk => by
      rw [← hpp k, hf.1.2 k hk, map_zero, smul_zero, sub_zero]
    have hD2m : D2 ∈ Ps := by
      refine ⟨⟨fun k => ?_, fun k hk => by simp [hD2, hf0 k hk]⟩, fun k => lE W Kt * g₁ k, ?_, fun k => by
        simp only [hD2]; ring⟩
      · simp only [hD2]
        rw [← hpp k]
        refine (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).2 (inId_lE W (inId_sub W ?_ ?_) _)
        · exact inId_aeval W hS _ _ ((Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).1 (hf.1.1 k))
        · exact inId_smul W ((Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).1 (hf.1.1 k)) _
      · have := Formalism.MainNotions.UnusedSlot80.UnivC.inNL_mulι W T₂ A c e b (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.KL.lA_mem W) Kt) hg₁
        simpa only [Formalism.MainNotions.UnusedSlot80.KL.ι_lE] using this
    have hSvk : ∀ k, Sv k = if k ∈ Rst then (∑ s ∈ Finset.range e, (lR ^ (Kt - Kk k) * xk k s) • Cg s +
        (lR ^ (Kt - Kk k) * x0k k) • Cg e) else 0 := by
      intro k
      simp only [hSv, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
      by_cases hk : k ∈ Rst
      · rw [if_pos hk, Finset.sum_eq_single k (fun k' _ hk' => by simp [Ne.symm hk']) (fun h => absurd hk h)]
        simp
      · rw [if_neg hk, Finset.sum_eq_zero]
        intro k' hk'
        have : k ≠ k' := fun h => hk (h ▸ hk')
        simp [this]
    have key : ∀ k ∈ Rst, (lR ^ Kt * t) • f k = (∑ s ∈ Finset.range e, (lR ^ (Kt - Kk k) * xk k s) • Cg s +
        (lR ^ (Kt - Kk k) * x0k k) • Cg e) + (lE W (Kt - Kk k) *
        (lE W (Kk k) * PPγ W e JS (f k) - ∑ s ∈ Finset.range e, xk k s • ιE (letE c * u s) -
          x0k k • ιE (letE c * (Λ * r₀))) - lE W Kt * (ιE W.π₀ * g₁ k)) := by
      intro k hk
      have hsplit : lE W Kt = lE W (Kt - Kk k) * lE W (Kk k) := by
        rw [← lE_add', Nat.sub_add_cancel (hKle k)]
      have hCe : Cg e = ιE (letE c * (Λ * r₀)) := by simp [hCg]
      have hCs : ∑ s ∈ Finset.range e, (lR ^ (Kt - Kk k) * xk k s) • Cg s =
          lE W (Kt - Kk k) * ∑ s ∈ Finset.range e, xk k s • ιE (letE c * u s) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s hs => ?_
        have : s < e := Finset.mem_range.1 hs
        simp only [hCg, this, if_true]
        rw [lE_smul, smul_smul]
      have e2 : t • f k = PPγ W e JS (f k) - ιE W.π₀ * g₁ k := by
        rw [← hpp k]; unfold PPγ; ring
      have e3 : (lR ^ Kt * t) • f k = lE W Kt * (t • f k) := by rw [lE_smul, smul_smul]
      have e4 : (lR ^ (Kt - Kk k) * x0k k) • Cg e = lE W (Kt - Kk k) * (x0k k • ιE (letE c * (Λ * r₀))) := by
        rw [hCe, lE_smul, smul_smul]
      rw [hCs, e4, e3, e2, hsplit]
      ring
    have heq : (lR ^ Kt * t) • f = Sv + (Rr - D2) := by
      funext k
      rw [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hSvk k]
      by_cases hk : k ∈ Rst
      · simp only [hRr, hD2, hk, if_true]; exact key k hk
      · simp only [hRr, hD2, hk, if_false, hf.1.2 k hk, smul_zero, hf0 k hk, mul_zero, sub_zero, add_zero]
    refine ⟨Kt, ?_⟩
    rw [heq]
    exact Submodule.add_mem_sup hSvm (Ps.sub_mem hRrm hD2m)
  have hsat : ∀ K : ℕ, ∀ f ∈ Ms, (lR ^ K * t) • f ∈ Ps → f ∈ Ps := by
    intro K f hf hKf
    obtain ⟨N, o, ho⟩ := eval_one_dvd_prime_pow W hKL hCA hinj hO2 e JS
    have h1 : (lR ^ (K + N)) • f ∈ Ps := by
      have := Ps.smul_mem o hKf
      rwa [smul_smul, show o * (lR ^ K * t) = lR ^ (K + N) by rw [pow_add, ← ho]; ring] at this
    obtain ⟨-, g, hg, hfg⟩ := h1
    obtain ⟨g', hg', hfg'⟩ := sat_l W hR T₂ A c e b (K + N) f hf.1 g hg (fun k => by
      rw [lE_smul]; exact hfg k)
    exact ⟨hf, g', hg', hfg'⟩
  obtain ⟨g₀, J, hg₀, hJ, hgen⟩ := gen_of_killer Ms Ps Is hIM F hfg lR t v' hK hsat
  refine ⟨g₀, J, ?_, fun i => ⟨(hJ i).1.1, (hJ i).1.2, (hJ i).2⟩, fun f hf1 hf2 hf3 => ?_⟩
  · calc g₀ ≤ Fintype.card ιv := hg₀
      _ = Rst.card * (e + 1) := by simp [ιv]
      _ ≤ m * Formalism.MainNotions.LocalTheoryWindows.ro A.ty A.len c * (A.len c + 1) := Nat.mul_le_mul_right _ hFO.2.1
  · obtain ⟨o, ho⟩ := hgen f ⟨⟨hf1, hf2⟩, hf3⟩
    obtain ⟨-, g, hg, hfg⟩ := ho
    refine ⟨o, g, hg, fun k => ?_⟩
    have := hfg k
    simpa [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] using this

end Formalism.MainNotions.UnusedSlot80.UGen
end
end

section
noncomputable section

open Classical PowerSeries

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def WF {O : Type} [CommRing O] (p : O) (F : PowerSeries O) (N : ℕ) : Prop :=
  ∃ g h : PowerSeries O, IsUnit (constantCoeff g) ∧ F = g * X ^ N + C p * h

theorem WF.mul {O : Type} [CommRing O] {p : O} {F F' : PowerSeries O} {N N' : ℕ} (h1 : WF p F N)
    (h2 : WF p F' N') : WF p (F * F') (N + N') := by
  obtain ⟨g, h, hg, rfl⟩ := h1
  obtain ⟨g', h', hg', rfl⟩ := h2
  refine ⟨g * g', g * X ^ N * h' + h * (g' * X ^ N' + C p * h'), by rw [map_mul]; exact hg.mul hg', ?_⟩
  rw [pow_add]; ring

theorem WF.one {O : Type} [CommRing O] (p : O) : WF p 1 0 :=
  ⟨1, 0, by simp, by simp⟩

theorem WF.X {O : Type} [CommRing O] (p : O) : WF p X 1 :=
  ⟨1, 0, by simp, by simp⟩

theorem WF.pow {O : Type} [CommRing O] {p : O} {F : PowerSeries O} {N : ℕ} (h : WF p F N) (k : ℕ) :
    WF p (F ^ k) (N * k) := by
  induction k with
  | zero => simpa using WF.one p
  | succ k ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul h

theorem WF.prod {O : Type} [CommRing O] {p : O} (F : ℕ → PowerSeries O) (N : ℕ → ℕ)
    (h : ∀ t, WF p (F t) (N t)) (e : ℕ) :
    WF p (∏ t ∈ Finset.range e, F t) (∑ t ∈ Finset.range e, N t) := by
  induction e with
  | zero => simpa using WF.one p
  | succ e ih => rw [Finset.prod_range_succ, Finset.sum_range_succ]; exact ih.mul (h e)

section Idem

variable {A : Type} [CommRing A] {E : A}

theorem idem_mul (_hE : E * E = E) {x y : A} (h : x * E = y * E) (z : A) : (z * x) * E = (z * y) * E := by
  rw [mul_assoc, h, ← mul_assoc]

theorem idem_pow (hE : E * E = E) {x y : A} (h : x * E = y * E) (k : ℕ) : x ^ k * E = y ^ k * E := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc x ^ (k + 1) * E = (x ^ k * E) * (x * E) := by rw [pow_succ]; linear_combination (-(x ^ k * x)) * hE
      _ = (y ^ k * E) * (y * E) := by rw [ih, h]
      _ = y ^ (k + 1) * E := by rw [pow_succ]; linear_combination (y ^ k * y) * hE

theorem idem_prod (hE : E * E = E) (x y : ℕ → A) (h : ∀ t, x t * E = y t * E) (e : ℕ) :
    (∏ t ∈ Finset.range e, x t) * E = (∏ t ∈ Finset.range e, y t) * E := by
  induction e with
  | zero => simp
  | succ e ih =>
    calc (∏ t ∈ Finset.range (e + 1), x t) * E = ((∏ t ∈ Finset.range e, x t) * E) * (x e * E) := by
          rw [Finset.prod_range_succ]; linear_combination (-((∏ t ∈ Finset.range e, x t) * x e)) * hE
      _ = ((∏ t ∈ Finset.range e, y t) * E) * (y e * E) := by rw [ih, h]
      _ = (∏ t ∈ Finset.range (e + 1), y t) * E := by
          rw [Finset.prod_range_succ]; linear_combination ((∏ t ∈ Finset.range e, y t) * y e) * hE

end Idem

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem evalZero_X_eq_uniformizer (W : LocWach PD LL O v n) (hR : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.Ring9 W) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W X = W.π₀ := by
  funext j
  rw [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_apply, subst_X (Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.hasSubst W hR)]
  rfl

theorem ps_letter [IsDomain O] (W : LocWach PD LL O v n) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hp0 : ((PD.p : ℕ) : O) ≠ 0) (a : ZMod n) (t : ℕ) :
    ∃ F : PowerSeries O, WF ((PD.p : ℕ) : O) F (PD.p ^ t) ∧
      Formalism.MainNotions.ArcLiftingSetup.ps W t * letE a = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W F * letE a := by
  obtain ⟨v, hvΔ, hvu, r, hr⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.modp hR hp0 t
  have hps : Formalism.MainNotions.ArcLiftingSetup.ps W t = v * W.π₀ ^ (PD.p ^ t) + ((PD.p : ℕ) : LetA O n) * (r + 1) := by
    have := Formalism.MainNotions.UnusedSlot80.ToolsR.pS_sub (W := W) t
    rw [hr] at this
    change Formalism.MainNotions.WachCoordinates.pS W t = _
    linear_combination this
  have hpsΔ : Formalism.MainNotions.ArcLiftingSetup.ps W t ∈ W.AΔ :=
    Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_AΔ t (Formalism.MainNotions.UnusedSlot80.ToolsR.qP_AΔ hR)
  have hpΔ : ((PD.p : ℕ) : LetA O n) ∈ W.AΔ := Subalgebra.natCast_mem _ _
  have hr1 : r + 1 ∈ W.AΔ := by
    refine Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ hpΔ (fun i => ?_) ?_
    · simp only [Pi.natCast_apply]
      exact_mod_cast (by
        intro h
        have := congrArg constantCoeff h
        simp only [map_natCast, map_zero] at this
        exact hp0 this : ((PD.p : ℕ) : PowerSeries O) ≠ 0)
    · have : ((PD.p : ℕ) : LetA O n) * (r + 1) = Formalism.MainNotions.ArcLiftingSetup.ps W t - v * W.π₀ ^ (PD.p ^ t) := by
        rw [hps]; ring
      rw [this]
      exact W.AΔ.sub_mem hpsΔ (W.AΔ.mul_mem hvΔ (W.AΔ.pow_mem hR.1 _))
  obtain ⟨gv, hgv⟩ := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.invariant_letter_eq_evaluation W hR hvΔ a
  obtain ⟨gr, hgr⟩ := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.invariant_letter_eq_evaluation W hR hr1 a
  have hE := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.letE_mul_self' (O := O) a
  refine ⟨gv * X ^ (PD.p ^ t) + C ((PD.p : ℕ) : O) * gr, ⟨gv, gr, ?_, rfl⟩, ?_⟩
  · have h1 := congrFun hgv a
    simp only [Pi.mul_apply, letE, Pi.single_eq_same, mul_one, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_apply] at h1
    have hva : IsUnit (v a) := hvu.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) a)
    rw [h1] at hva
    have := hva.map constantCoeff
    rwa [Formalism.MainNotions.UnusedSlot80.ToolsR.cc_subst (Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR)] at this
  · have hC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (C ((PD.p : ℕ) : O)) = ((PD.p : ℕ) : LetA O n) := by
      rw [map_natCast, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, map_natCast]
    have hX : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (X ^ (PD.p ^ t)) = W.π₀ ^ (PD.p ^ t) := by
      rw [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, map_pow, ← Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, evalZero_X_eq_uniformizer W hR]
    rw [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_add W hR, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evalZero_mul W hR, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evalZero_mul W hR, hX, hC,
      hps]
    linear_combination (W.π₀ ^ (PD.p ^ t)) * hgv + ((PD.p : ℕ) : LetA O n) * hgr

theorem finLev_of [IsDomain O] (W : LocWach PD LL O v n) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hp0 : ((PD.p : ℕ) : O) ≠ 0) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) : FinLev W := by
  intro a e H
  set pO : O := ((PD.p : ℕ) : O) with hpO
  set I : Ideal O := Ideal.span {pO} with hI
  have hE := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.letE_mul_self' (O := O) a
  choose Fs hFs hFe using fun t => ps_letter W hR hp0 a t
  set Gall : PowerSeries O := X * (∏ t ∈ Finset.range e, Fs t ^ H t) ^ 2 with hGall
  have hWF : WF pO Gall (1 + (∑ t ∈ Finset.range e, PD.p ^ t * H t) * 2) :=
    (WF.X pO).mul ((WF.prod (fun t => Fs t ^ H t) (fun t => PD.p ^ t * H t)
      (fun t => (hFs t).pow (H t)) e).pow 2)
  set D := 1 + (∑ t ∈ Finset.range e, PD.p ^ t * H t) * 2 with hD
  have hlet : W.π₀ * (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ H t) ^ 2 * letE a =
      Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W Gall * letE a := by
    have h1 : (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ H t) * letE a =
        (∏ t ∈ Finset.range e, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (Fs t) ^ H t) * letE a :=
      idem_prod hE _ _ (fun t => idem_pow hE (hFe t) (H t)) e
    have h2 := idem_mul hE (idem_pow hE h1 2) W.π₀
    rw [h2, hGall, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, map_mul, map_pow, map_prod, ← Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR,
      evalZero_X_eq_uniformizer W hR]
    simp only [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, map_pow]
  obtain ⟨g, h, hgu, hGe⟩ := hWF
  obtain ⟨P, uu, huu, hPm, hPd, hPc, hGP⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.weierP pO hpu D g h hgu
  have hmapP : (P : PowerSeries O).map (Ideal.Quotient.mk I) = X ^ D := by
    ext k
    rw [coeff_map, Polynomial.coeff_coe, coeff_X_pow]
    split_ifs with hk
    · subst hk; rw [← hPd, hPm.coeff_natDegree, map_one]
    · rcases lt_or_gt_of_ne hk with hlt | hgt
      · exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (hPc k hlt))
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  haveI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, hI, Ideal.span_singleton_eq_top]; exact hpu)
  have hord : ((P : PowerSeries O).map (Ideal.Quotient.mk I)).order.toNat = D := by
    rw [hmapP, order_X_pow]; rfl
  have hdiv : (P : PowerSeries O).IsWeierstrassDivisorAt I := by
    unfold PowerSeries.IsWeierstrassDivisorAt
    rw [hord, Polynomial.coeff_coe, ← hPd, hPm.coeff_natDegree]
    exact isUnit_one
  refine ⟨D, fun u hu => ?_⟩
  obtain ⟨f, hf⟩ := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.invariant_letter_eq_evaluation W hR hu a
  have HD := hdiv.isWeierstrassDivisionAt_div_mod f
  set q := hdiv.div f
  set r := hdiv.mod f
  have hdeg : r.degree < (D : WithBot ℕ) := by
    have := HD.degree_lt
    rw [hord] at this
    exact this
  have heq : f = (P : PowerSeries O) * q + (r : PowerSeries O) := HD.eq_mul_add
  have hfG : f = Gall * (↑huu.unit⁻¹ * q) + (r : PowerSeries O) := by
    rw [heq, hGe, hGP, mul_assoc, ← mul_assoc uu, IsUnit.mul_val_inv, one_mul]
  refine ⟨fun j => r.coeff j, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (↑huu.unit⁻¹ * q),
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_mem_invariants W hR _, ?_⟩
  have hr : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (r : PowerSeries O) =
      ∑ j : Fin D, algebraMap O (LetA O n) (r.coeff j) * W.π₀ ^ (j : ℕ) := by
    rw [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, Formalism.MainNotions.RamifiedCoefficientChains.S9.Ring.algHom_coe, ← Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR,
      evalZero_X_eq_uniformizer W hR]
    have hnd : r.natDegree < D := by
      by_cases hr0 : r = 0
      · rw [hr0, Polynomial.natDegree_zero]; omega
      · exact (Polynomial.natDegree_lt_iff_degree_lt hr0).2 hdeg
    rw [Polynomial.aeval_eq_sum_range' hnd, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
  have hu' : (letE a : LetA O n) * u = letE a * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f := by
    rw [mul_comm, hf, mul_comm]
  rw [hu', hfG, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_add W hR, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evalZero_mul W hR, hr]
  have h3 : (letE a : LetA O n) * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W Gall =
      W.π₀ * (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ H t) ^ 2 * letE a := by
    rw [hlet, mul_comm]
  linear_combination (Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (↑huu.unit⁻¹ * q)) * h3

end Formalism.MainNotions.UnusedSlot80.UGen
end
end

section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem univGenCore_of_lev [IsDomain O] [IsPrincipalIdealRing O] [NeZero n]
    [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O))
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hKL : KillerLevCore W) (hS : PsStable W)
    (hRAT : CutU.RATCore W)
    (hInv : ∀ (A : ArcP n) (c : ZMod n), c ∈ A.cuts → ∀ s < A.len c, InvLevAt W s) :
    Formalism.MainNotions.UnusedSlot80.UnivC.UnivGenCore PD W :=
  univGenCore_of' W hinj hO2 hpu hR hKL hS hRAT hInv (finLev_of W hR (p_ne_zero_O' W) hpu)

theorem universal_generators_of_units [IsDomain O] [IsPrincipalIdealRing O] [NeZero n]
    [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) :
    Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W → KillerLevCore W → PsStable W → W.π₀ ∈ W.AΔ →
      CutU.RATCore W → CutU.InvLevCore W → Formalism.MainNotions.UnusedSlot80.UnivC.UnivGenCore PD W :=
  fun hR hKL hS _ hRAT hInv =>
    univGenCore_of_lev W hinj hO2 hpu hR hKL hS hRAT fun _ _ _ s _ => invLevAt_of W hInv s

end Formalism.MainNotions.UnusedSlot80.UGen
end
end
