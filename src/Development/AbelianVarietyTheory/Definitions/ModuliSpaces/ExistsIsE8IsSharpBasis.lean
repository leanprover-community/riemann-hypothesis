import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Definitions.Degenerations.LabKerUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZM.Model

theorem isE8_W8 : IsE8 W8 := by
  unfold IsE8
  rw [w8_add_transpose_eq_e8]
  exact ⟨e8_posDef, e8_det_eq_one⟩




section Away
variable {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ) {n : ℕ} (hn : n ≠ 0)

def awayEmb : Localization.Away (n : 𝓞 F) →+* ℂ :=
  IsLocalization.Away.lift (n : 𝓞 F) (g := φ.comp (algebraMap (𝓞 F) F)) (by simpa using hn)


def tbaseAway (z : 𝓞 F) (hz : IsPrimitiveRoot z n) : TBase (Localization.Away (n : 𝓞 F)) n where
  ζ := Units.map (algebraMap (𝓞 F) (Localization.Away (n : 𝓞 F))).toMonoidHom (hz.isUnit hn).unit
  unit := by simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (n : 𝓞 F)) (n : 𝓞 F)
  prim := by
    intro K _ β
    have hu : IsUnit (n : Localization.Away (n : 𝓞 F)) := by
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (n : 𝓞 F)) (n : 𝓞 F)
    haveI : NeZero (n : K) := ⟨by simpa using (hu.map β).ne_zero⟩
    have h0 := (hz.isRoot_cyclotomic (Nat.pos_of_ne_zero hn)).map
      (f := β.comp (algebraMap (𝓞 F) (Localization.Away (n : 𝓞 F))))
    rw [Polynomial.map_cyclotomic] at h0
    simpa using Polynomial.isRoot_cyclotomic_iff.1 h0
end Away

section Basis
variable (h : ℕ)

def halves (g : ℕ) : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)

theorem halves_inl (g : ℕ) (a : Fin g) : (halves g (.inl a) : ℕ) = a := by simp [halves]
theorem halves_inr (g : ℕ) (a : Fin g) : (halves g (.inr a) : ℕ) = g + a := by simp [halves, add_comm]

theorem sum_halves (g : ℕ) (i j : Fin (2 * g)) :
    ∑ a : Fin g, ((Pi.single i 1 : Fin (2 * g) → ℤ) (halves g (.inl a)) * (Pi.single j 1 : Fin (2 * g) → ℤ) (halves g (.inr a)) -
      (Pi.single i 1 : Fin (2 * g) → ℤ) (halves g (.inr a)) * (Pi.single j 1 : Fin (2 * g) → ℤ) (halves g (.inl a))) =
      Out.stdSymp g i j := by
  obtain ⟨i, rfl⟩ := (halves g).surjective i
  obtain ⟨j, rfl⟩ := (halves g).surjective j
  unfold Out.stdSymp
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Pi.single_apply, (halves g).injective.eq_iff, halves_inl, halves_inr, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, if_false, mul_zero, zero_mul, sub_zero, zero_sub, ite_mul, one_mul, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
  all_goals
    try simp only [Fin.ext_iff]
    have := i.2
    have := j.2
    split_ifs <;> omega

def sharpBas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) where
  toFun x u := Sum.elim (fun i => x (halves _ (.inl (finProdFinEquiv (u, i)))))
    (fun i => ∑ v, E8inv u v * x (halves _ (.inr (finProdFinEquiv (v, i)))))
  invFun y k := Sum.elim (fun a => y (finProdFinEquiv.symm a).1 (.inl (finProdFinEquiv.symm a).2))
    (fun a => ∑ v, E8 (finProdFinEquiv.symm a).1 v * y v (.inr (finProdFinEquiv.symm a).2)) ((halves _).symm k)
  map_add' x y := by
    funext u i; rcases i with i | i <;> simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext u i; rcases i with i | i <;> simp [Finset.mul_sum, mul_left_comm]
  left_inv x := by
    funext k
    obtain ⟨k, rfl⟩ := (halves _).surjective k
    rcases k with a | a
    · simp only [Equiv.symm_apply_apply, Sum.elim_inl, Prod.mk.eta, Equiv.apply_symm_apply]
    · obtain ⟨⟨u, i⟩, rfl⟩ := finProdFinEquiv.surjective a
      simp only [Equiv.symm_apply_apply, Sum.elim_inr, Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← Matrix.mul_apply, e8_mul_e8inv, Matrix.one_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
  right_inv y := by
    funext u i
    rcases i with i | i
    · simp only [Equiv.symm_apply_apply, Sum.elim_inl]
    · simp only [Equiv.symm_apply_apply, Sum.elim_inr, Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← Matrix.mul_apply, e8inv_mul_e8, Matrix.one_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem dual_sum (y : Fin 8 → ℤ) (u : Fin 8) : ∑ v, E8 u v * ∑ w, E8inv v w * y w = y u := by
  have : E8.mulVec (E8inv.mulVec y) = y := by rw [Matrix.mulVec_mulVec, e8_mul_e8inv, Matrix.one_mulVec]
  exact congrFun this u

theorem sharp_form (x x' : Fin (2 * (8 * h)) → ℤ) :
    ∑ u, ∑ v, E8 u v * omegaStd (sharpBas h x u) (sharpBas h x' v) =
      ∑ a : Fin (8 * h), (x (halves _ (.inl a)) * x' (halves _ (.inr a)) - x (halves _ (.inr a)) * x' (halves _ (.inl a))) := by
  have hs : ∀ u v, E8 u v = E8 v u := fun u v => congrFun (congrFun e8_transpose v) u
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  have key : ∀ (A B : Fin 8 → Fin h → ℤ), ∑ u, ∑ v, ∑ i, E8 u v * (A u i * ∑ w, E8inv v w * B w i) = ∑ u, ∑ i, A u i * B u i := by
    intro A B
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← dual_sum (fun w => B w i) u, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have k1 := key (fun u i => x (halves _ (.inl (finProdFinEquiv (u, i))))) (fun u i => x' (halves _ (.inr (finProdFinEquiv (u, i)))))
  have k2 := key (fun u i => x' (halves _ (.inl (finProdFinEquiv (u, i))))) (fun u i => x (halves _ (.inr (finProdFinEquiv (u, i)))))
  rw [Finset.sum_comm] at k2
  simp only [Finset.sum_sub_distrib]
  rw [← k1, show (∑ u, ∑ i, x (halves _ (.inr (finProdFinEquiv (u, i)))) * x' (halves _ (.inl (finProdFinEquiv (u, i))))) =
    ∑ u, ∑ i, x' (halves _ (.inl (finProdFinEquiv (u, i)))) * x (halves _ (.inr (finProdFinEquiv (u, i)))) from by
      simp only [mul_comm], ← k2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_sub_distrib, omegaStd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hs v u]
  simp only [sharpBas, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
  ring

theorem isSharpBasis_sharpBas : IsSharpBasis W8 (sharpBas h) := by
  intro i j
  rw [w8_add_transpose_eq_e8, sharp_form, sum_halves]

end Basis

theorem exists_isE8_isSharpBasis : ∃ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W ∧ ∀ h : ℕ,
    ∃ bas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)), IsSharpBasis W bas :=
  ⟨W8, isE8_W8, fun h => ⟨sharpBas h, isSharpBasis_sharpBas h⟩⟩


section Use
open AlgebraicGeometry CategoryTheory MonObj
variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}


end Use

section Zero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi Out.Inh
open scoped CategoryTheory.Obj
variable {o : Type} [CommRing o] {S : Scheme.{0}} {k : ℕ} {J : Type}

theorem corr_comm_pull {X X' Y : Scheme.{0}} (f : X ⟶ X') {K : Type} [Fintype K] (φ φ' : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb ((trivLB X').pull f) φ ε)) (b : LB.Gen (LB.LinComb ((trivLB X').pull f) φ' ε)) (h h' : Y ⟶ Y)
    (hh : h = 𝟙 Y) (hh' : h' = 𝟙 Y)
    (c : LB.Gen (LB.LinComb ((trivLB X').pull f) (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim)) (hc : ∀ j, c.s j = 1) :
    LB.Gen.Corr ((trivLB X').pull f) _ _ _ _ (LB.mulGen _ _ _ _ _ a (LB.pullGen _ _ _ b h))
      (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ b (LB.pullGen _ _ _ a h')) c) := by
  subst hh hh'
  intro j j'
  obtain rfl : j = fun _ _ => PUnit.unit := rfl
  obtain rfl : j' = fun _ _ => PUnit.unit := rfl
  intro _ _ _
  have e1 : ∀ (V W : Y.Opens) (h1 : V ≤ W) (U U' : Y.Opens) (h2 : W ≤ U) (h3 : W ≤ U') (u : Γ(Y, U)ˣ) (v : Γ(Y, U')ˣ),
      res h1 (res h2 u * res h3 v) = res (h1.trans h2) u * res (h1.trans h3) v := by
    intros; rw [map_mul, ZH.RealModel.res_res, ZH.RealModel.res_res]
  refine (e1 _ _ _ _ _ _ _ _ _).trans (Eq.trans ?_ (e1 _ _ _ _ _ _ _ _ _).symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (e1 _ _ _ _ _ _ _ _ _) ((congrArg _ (hc _)).trans (ZH.RealModel.res_one _))).symm
  rw [_root_.mul_one, _root_.mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (ZH.RealModel.res_res _ _ _)
  · exact (ZH.RealModel.res_res _ _ _).symm

theorem isGen_one {X : Scheme.{0}} (L : LB X) (hL : ∀ i j, L.g i j = 1) : (⟨fun _ => 1⟩ : L.Gen).IsGen := by
  intro i j; rw [hL, _root_.one_mul]; exact (map_one _).trans (map_one _).symm

theorem weil_pull_zero {X : Scheme.{0}} (f : (𝟙_ (Over S)).left ⟶ X) (n : ℤ) {T : Over S} (x y : T ⟶ 𝟙_ (Over S)) :
    Out.WeilIs (𝟙_ (Over S)) ((trivLB X).pull f) n x y 1 := by
  intro p
  refine ⟨⊤, trivial, ⟨⟨_, _, isGen_one _ (linComb_g_one _ (linComb_triv_g _ _) _ _)⟩,
    ⟨_, _, isGen_one _ (linComb_g_one _ (linComb_triv_g _ _) _ _)⟩, rfl, rfl⟩, ?_⟩
  intro θx θy _ _
  have hc : Out.unitRes (T := T) ⊤ 1 = 1 := map_one _
  rw [hc]
  exact corr_comm_pull _ _ _ _ _ _ _ _ (ZH.RealModel.translT_id S _) (ZH.RealModel.translT_id S _) _
    (fun j => (congrArg _ (map_one _)).trans (ZH.RealModel.res_one _))


def zeroSieg (ζ : o) (s : S ⟶ Sp o) : SiegPre 0 k ζ s where
  A := 𝟙_ (Over S)
  ab := UU.isAbelianScheme_unit S
  P := trivLB _
  isLB := trivLB_isLB _
  rig₁ := ⟨_, ZH.RealModel.oneG_gen _ _⟩
  rig₂ := ⟨_, ZH.RealModel.oneG_gen _ _⟩
  symm := lbIso_of_g _ _ (fun _ _ => rfl) (linComb_triv_g _ _)
  lev := fun _ => 𝟙 _
  lev_add := fun _ _ => toUnit_unique _ _
  lev_tors := fun _ => toUnit_unique _ _
  geom := fun K _ _ x β z _ _ => ⟨fun a => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => toUnit_unique _ _⟩,
    fun g _ => ⟨0, toUnit_unique _ _⟩, fun a b => by
      have : unitOn (z ^ (2 * omegaStd a b)) = 1 := by simp [omegaStd, unitOn]
      rw [this]; exact weil_pull_zero _ _ _ _⟩







end Zero

end GlobalTheory.ZM.Model
end
