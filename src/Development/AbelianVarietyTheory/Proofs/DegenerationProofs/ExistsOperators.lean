import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaReal

open CommPairing GlobalLift VVRank ThetaCoord

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem exists_symLift_one (hL : L.IsLB) {k : ℤ} {ν : LB.Gen (negLB A L k T)} (hν : ν.IsGen) :
    ∃ θ : ThetaGrp A L k T, SymLift A L k 1 1 θ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → tval θ r z J = 1 := by
  have h1 : (LB.oneGen L (Y := (T ⊗ A).left)).IsGen := SymLiftOdd.isGen_of_gm fun y j j' _ _ => by
    rw [trF, Fintype.prod_empty, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A (1 : T ⟶ A)).left]) (ε' := ![k, -k])
    (fun U _ f => by
      rw [Fintype.prod_empty, Fin.prod_univ_two, ThetaAct.translPt_one]
      simp) (LB.oneGen L) h1
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval (⟨1, t, ht⟩ : ThetaGrp A L k T) r z J = 1 := fun Z r z J hJ => (hv Z r z J hJ).trans (val_one _)
  refine ⟨⟨1, t, ht⟩, symLift_of_tval hL rfl hν (fun T' π z J hJ p => ?_) (fun T' π z J hJ p => ?_), hv'⟩
  · exact Finset.prod_eq_one fun _ _ => hv' _ _ _ _ hJ
  · rw [hv' _ _ _ _ hJ, hv' _ _ _ _ hJ, MonObj.comp_one, inv_one, _root_.one_mul, _root_.one_mul, _root_.one_mul,
      mul_inv_cancel]

theorem isActOf_self (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB)
    {ν : LB.Gen (negLB A L 1 T)} (hν : ν.IsGen) {a : ℤ} {m q : ℕ} (hq : Odd q)
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -1])} (hα : α.IsGen)
    {th : LB.Sec (LPow A L 1 T)} {s : LB.Sec (LPow A L a T)}
    (hs : IsTwistPull A L (mulT A T m) (snd T A ^ m) (lift_snd _ _) a 1 α th s)
    {y : T ⟶ A} (hm : y ^ m = 1) (hy : y ^ q = 1) {θ : ThetaGrp A L a T} (H : SymLift A L a q y θ) :
    IsActOf A L a θ s s := by
  have := hA.comm
  obtain ⟨θ₁, h₁, v₁⟩ := exists_symLift_one hL hν
  obtain ⟨θ', h', v'⟩ := exists_symLift_mulPull hA hL (one_dvd q) hα hy (hm.symm ▸ h₁)
  have hc := SymLiftOdd.symLift_unique hG hA hL hq θ θ' H h'
  refine isTwistPull_of_sv A hL θ.isGen fun z J hJ => ?_
  have e : tval θ (𝟙 _) z J = tval θ' (𝟙 _) z J := val_corr hJ hc _
  have e₁ := sv_mulPull hs (fst T A) hJ (snd T A)
  have e₂ := sv_mulPull hs (fst T A) hJ ((fst T A ≫ y) * snd T A)
  have e₃ := v' _ (fst T A) z J hJ (snd T A)
  rw [v₁ _ _ _ _ hJ, _root_.mul_one] at e₃
  rw [mul_pow, ← MonObj.comp_pow, hm, MonObj.comp_one, _root_.one_mul] at e₂
  change _ = (tval θ (𝟙 _) z J).val * _
  rw [e, SymLiftOdd.id_eq_lift, ThetaCoord.lift_translT, H.pt_eq, e₃, e₁, e₂, Units.val_mul, _root_.mul_assoc,
    Units.inv_mul_cancel_left]

theorem act_act (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {k : ℤ} {q : ℕ} (hq : Odd q) {x y : T ⟶ A}
    (hy : y ^ q = 1) {θx θy θ : ThetaGrp A L k T} (Hx : SymLift A L k q x θx) (Hy : SymLift A L k q y θy)
    (H : SymLift A L k q (y * x) θ) {c : Γ(T.left, ⊤)ˣ} (hc : WeilIs A L k x y c)
    {s s' s'' t : LB.Sec (LPow A L k T)} (h₁ : IsActOf A L k θy s s') (h₂ : IsActOf A L k θx s' s'')
    (h₃ : IsActOf A L k θ s t) :
    (SecM.ofSec A s'' : SecM A L k T) = ((c ^ ((q + 1) / 2) : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) • SecM.ofSec A t := by
  refine ThetaAct.sv_ext hL fun z J hJ => ?_
  have e₁ := sv_act Hx.pt_eq h₂ (fst T A) hJ (snd T A)
  have e₂ := sv_act Hy.pt_eq h₁ (fst T A) hJ ((fst T A ≫ x) * snd T A)
  have e₃ := sv_act H.pt_eq h₃ (fst T A) hJ (snd T A)
  have e₄ := tval_mul hG hA hL hq hy Hx Hy H hc (fst T A) hJ (snd T A)
  rw [← _root_.mul_assoc, ← MonObj.comp_mul] at e₂
  rw [ThetaAct.sv_smul _ _ _ _ hJ, Category.id_comp, gs_unit _ _ ⊤ trivial, map_pow, SymLiftOdd.id_eq_lift]
  refine e₁.trans ?_
  rw [e₂, ← _root_.mul_assoc, ← Units.val_mul, e₄, Units.val_mul, _root_.mul_assoc, ← e₃]
  rfl

theorem sum_iff {k : ℤ} {κ : Type} [Fintype κ] (σ : LB.Sec (LPow A L k T)) (s : κ → SecM A L k T)
    (c : κ → Γ(T.left, ⊤)) :
    (∀ j, σ.f j = ∑ i, liftFun A _ (c i) * (SecM.toSec A (s i)).f j) ↔ SecM.ofSec A σ = ∑ i, c i • s i := by
  have e : ∀ j, (∑ i, c i • s i : SecM A L k T).1 j = ∑ i, liftFun A _ (c i) * (SecM.toSec A (s i)).f j := fun j => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  exact ⟨fun h => Subtype.ext (funext fun j => (h j).trans (e j).symm),
    fun h j => (congrArg (fun q => q.1 j) h).trans (e j)⟩

theorem existsUnique_of_basis {k : ℤ} {κ : Type} [Fintype κ] (s : Module.Basis κ Γ(T.left, ⊤) (SecM A L k T))
    (σ : LB.Sec (LPow A L k T)) :
    ∃! c : κ → Γ(T.left, ⊤), ∀ j, σ.f j = ∑ i, liftFun A _ (c i) * (SecM.toSec A (s i)).f j := by
  simp only [sum_iff]
  exact ⟨s.equivFun (SecM.ofSec A σ), (s.sum_equivFun _).symm, fun c hc => by
    rw [hc, ← s.equivFun_symm_apply, LinearEquiv.apply_symm_apply]⟩

theorem UnivBasis.exists_basis {P : PolAV S} [IsAffine T.left] {n : ℤ} {κ : Type} {b : κ → SecM P.A P.L n T}
    (h : UnivBasis P n b) : ∃ c : Module.Basis κ Γ(T.left, ⊤) (SecM P.A P.L n T), ∀ i, c i = b i := by
  obtain ⟨c, hc⟩ := h T (𝟙 T)
  exact ⟨c, fun i => (hc i).trans (pullM_id P.A P.isLB n _)⟩

theorem UnivBasis.unique {P : PolAV S} {n : ℤ} {κ : Type} [Unique κ] {b : κ → SecM P.A P.L n T}
    (h : UnivBasis P n b) : UnivBasis P n (fun _ : Fin 1 => b default) := fun T' _ u => by
  obtain ⟨c, hc⟩ := h T' u
  refine ⟨c.reindex (Equiv.ofUnique κ (Fin 1)), fun i => ?_⟩
  rw [Module.Basis.reindex_apply, hc, Subsingleton.elim ((Equiv.ofUnique κ (Fin 1)).symm i) default]

end GlobalTheory.ThetaReal
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaReal

theorem pt_nsmul {G H : Type} [AddCommGroup G] [Group H] (pt : G → H) (h : ∀ a b, pt (a + b) = pt a * pt b) :
    pt 0 = 1 ∧ ∀ (n : ℕ) a, pt (n • a) = pt a ^ n := by
  have h0 : pt 0 = 1 := by
    have := h 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  refine ⟨h0, fun n a => ?_⟩
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

theorem eStd_nsmul (g M r : ℕ) (a b : Fin g ⊕ Fin g → ZMod M) : eStd g M a (r • b) = r • eStd g M a b := by
  simp only [eStd, Finset.smul_sum, Pi.smul_apply, nsmul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem nsmul_self {κ : Type} (M : ℕ) (a : κ → ZMod M) : M • a = 0 := by
  funext i
  simp

theorem exists_operators (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {g m r N : ℕ}
    (hN : N = m ^ 2) (hm : Odd m) (hu : IsUnit ((r * N : ℕ) : Γ(S, ⊤))) (ze : Γ(S, ⊤)ˣ)
    (pt : (Fin g ⊕ Fin g → ZMod (r * N)) → (baseOver S ⟶ P.A)) (hadd : ∀ a b, pt (a + b) = pt a * pt b)
    (hw : ∀ a b, WeilIs P.A P.L (r * N : ℕ) (pt a) (pt b) (ze ^ (r * N * (eStd g (r * N) a b).val)))
    (U : (Fin g ⊕ Fin g → ZMod (r * N)) → ThetaGrp P.A P.L N (baseOver S))
    (hU : ∀ a, SymLift P.A P.L N N (pt (r • a)) (U a))
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver S) P.A).left, (snd (baseOver S) P.A ^ m).left]
      ![(N : ℤ), -1])} (hα : α.IsGen) {th : LB.Sec (LPow P.A P.L 1 (baseOver S))}
    {s₀ : LB.Sec (LPow P.A P.L N (baseOver S))}
    (hs : IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) N 1 α th s₀) :
    ∃ u : (Fin g ⊕ Fin g → ZMod (r * N)) →
        SecM P.A P.L N (baseOver S) →ₗ[Γ((baseOver S).left, ⊤)] SecM P.A P.L N (baseOver S),
      (∀ a s s', IsActOf P.A P.L N (U a) s s' ↔ u a (SecM.ofSec P.A s) = SecM.ofSec P.A s') ∧
      (∀ a, r • a = 0 → ∀ v, u a v = v) ∧
      (∀ a b, ∃ e : ℕ, ∀ v, u a (u b v) = (show Γ((baseOver S).left, ⊤) from ze.val ^ e) • u (a + b) v) ∧
      (∀ a b, r • eStd g _ a b = 0 → ∀ v, u a (u b v) = u (a + b) v) ∧
      ∀ a, (r * m) • a = 0 → u a (SecM.ofSec P.A s₀) = SecM.ofSec P.A s₀ := by
  obtain ⟨ρ, hρ, -⟩ := GlobalTheory.thetaGrp_acts_linearly hL.globalFns S P N (baseOver S)
  obtain ⟨h0, hsm⟩ := pt_nsmul pt hadd
  have hodd : Odd N := hN ▸ hm.pow
  have tors : ∀ a, pt (r • a) ^ N = 1 := fun a => by rw [← hsm, smul_smul, mul_comm N r, nsmul_self, h0]
  have act : ∀ a v, IsActOf P.A P.L N (U a) (SecM.toSec P.A v) (SecM.toSec P.A (ρ (U a) v)) := fun a v =>
    (hρ _ _ _).2 rfl
  have weil : ∀ a b, WeilIs P.A P.L N (pt (r • a)) (pt (r • b))
      (ze ^ (r * N * (r • eStd g (r * N) a b).val)) := fun a b => by
    have h₁ := hw a (r • b)
    rw [eStd_nsmul] at h₁
    have h₂ := (hL.weil S P N (baseOver S)).2.2.2 r (pt a) (pt (r • b))
      (ze ^ (r * N * (r • eStd g (r * N) a b).val)) (by rw [mul_comm]; exact hu)
      (by rw [← hsm, mul_comm N r, nsmul_self, h0]) (tors b)
    rw [hsm r a]
    refine h₂.1 ?_
    rw [← Nat.cast_mul, mul_comm N r]
    exact h₁
  have key : ∀ a b v, ρ (U a) (ρ (U b) v) = (show Γ((baseOver S).left, ⊤) from
      ze.val ^ (r * N * (r • eStd g (r * N) a b).val * ((N + 1) / 2))) • ρ (U (a + b)) v := fun a b v => by
    have := act_act hL.globalFns P.isAb P.isLB hodd (tors b) (hU a) (hU b)
      (by rw [← hadd, ← smul_add, add_comm]; exact hU (a + b)) (weil a b) (act b v) (act a _) (act (a + b) v)
    refine this.trans (congrArg (· • _) ?_)
    rw [pow_mul ze.val]
    exact (Units.val_pow_eq_pow_val _ _).trans (congrArg (· ^ _) (Units.val_pow_eq_pow_val _ _))
  refine ⟨fun a => (ρ (U a)).toLinearMap, fun a => hρ _, fun a ha v => ?_, fun a b => ⟨_, key a b⟩,
    fun a b h v => ?_, fun a ha => (hρ _ _ _).1 ?_⟩
  · have h₁ : SymLift P.A P.L N N 1 (U a) := by
      have := hU a
      rwa [ha, h0] at this
    have := act_act hL.globalFns P.isAb P.isLB hodd (one_pow N) h₁ h₁ (by rw [_root_.mul_one]; exact h₁)
      ((hL.weil S P N (baseOver S)).2.2.1 1 (one_pow N)) (act a v) (act a _) (act a v)
    rw [one_pow, Units.val_one, one_smul] at this
    exact (ρ (U a)).injective this
  · refine (key a b v).trans ?_
    rw [h, ZMod.val_zero, mul_zero, zero_mul, pow_zero]
    exact one_smul _ _
  · obtain ⟨ν, hν⟩ := GlobalTheory.exists_gen_negLB hL.globalFns S P 1 (baseOver S)
    exact isActOf_self hL.globalFns P.isAb P.isLB hν hodd hα hs
      (by rw [← hsm, smul_smul, mul_comm m r, ha, h0]) (tors a) (hU a)

end GlobalTheory.ThetaReal
end
end
