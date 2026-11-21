import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.TorusExtChar

open CubeValues SymmetricSemicharacter FrameValue

theorem fn_ext_val {U : (Sp ℂ).Opens} {a b : Γ(Sp ℂ, U)}
    (h : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ U → valAt' (𝟙 (Sp ℂ)) U a = valAt' (𝟙 (Sp ℂ)) U b) : a = b := by
  by_cases hU : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ U
  · have e := h hU
    obtain rfl : U = ⊤ := top_le_iff.1 hU
    rw [valAt', valAt', dif_pos hU, dif_pos hU, valAt, valAt] at e
    have e' := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 e
    have r : ∀ a : Γ(Sp ℂ, ⊤), ((𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ).appLE ⊤ ⊤ hU).hom a = a := fun a =>
      congrArg (fun q => q.hom a) ((Sp ℂ).presheaf.map_id (Opposite.op ⊤))
    exact (r a).symm.trans (Eq.trans e' (r b))
  · refine fn_ext fun x hx => (hU fun y _ => ?_).elim
    obtain rfl : x = y := Subsingleton.elim (α := PrimeSpectrum ℂ) x y
    exact hx

theorem exists_unit_val (U : (Sp ℂ).Opens) (c : ℂ) (hc : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ U → c ≠ 0) :
    ∃ a : Γ(Sp ℂ, U)ˣ, ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ U → valAt' (𝟙 (Sp ℂ)) U a.val = c := by
  by_cases hU : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ U
  · have v := fun a => (valueRules _ (𝟙 (Sp ℂ))).2.2.2.2.2 (𝟙 _) (Category.id_comp _) U a hU
    obtain ⟨e, he⟩ := (valueRules _ (𝟙 (Sp ℂ))).2.1 U hU
    have m : constFn (𝟙 (Sp ℂ)) U c * constFn (𝟙 (Sp ℂ)) U c⁻¹ = 1 := fn_ext_val fun _ => by
      rw [he, he, map_mul, ← he, ← he, v, v, map_one, mul_inv_cancel₀ (hc hU)]
    exact ⟨Units.mkOfMulEqOne _ _ m, fun _ => v c⟩
  · exact ⟨1, fun h => (hU h).elim⟩

section Gen

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Sp ℂ ⟶ A.left)} {ε : K → ℤ} {φ' : K' → (Sp ℂ ⟶ A.left)} {ε' : K' → ℤ}

theorem corr_of_genVal (hL : L.IsLB) {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (ht : t.IsGen) (ht' : t'.IsGen) {z : K → Fin g → ℂ} {z' : K' → Fin g → ℂ}
    (hz : IsLift u φ (𝟙 _) z) (hz' : IsLift u φ' (𝟙 _) z')
    (hs : ∀ f : (Fin g → ℂ) → ℂˣ, ∏ k, f (z k) ^ ε k = ∏ k, f (z' k) ^ ε' k)
    (h : genVal u hL t (𝟙 _) z = genVal u hL t' (𝟙 _) z') : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  refine Units.ext (fn_ext_val fun h₃ => ?_)
  obtain ⟨h₁, h₂⟩ := (le_preimage_inf _ _ _).1 h₃
  refine (val_res _ valueRules inf_le_left h₃ _).trans (Eq.trans ?_ (val_res _ valueRules inf_le_right h₃ _).symm)
  refine (valAt'_gen hL ht hz h₁).trans (Eq.trans ?_ (valAt'_gen hL ht' hz' h₂).symm)
  rw [h]
  congr 1
  obtain ⟨J, hJ, e⟩ := exists_good L hL (default : PrimeSpectrum ℂ) (Sum.elim φ φ') (Sum.elim j j') (by
    rintro (a | a) (b | b) e
    exacts [c₁ a b e, c₃ a b e, (c₃ b a e.symm).symm, c₂ a b e]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 (h₁ trivial) a, Set.mem_iInter.1 (h₂ trivial) a])
  have := congrArg (Units.coeHom ℂ) (hs fun w => Units.mk0 _ (u.fr_ne (J (u.ex w).left) w
    (((valueRules _ (u.ex w).left).1 _).2 (hJ _))))
  simp only [map_prod, map_zpow, Units.coeHom_apply, Units.val_mk0] at this
  have a : ∀ k, J (u.ex (z k)).left = j k := fun k => by
    rw [← hz k, Category.id_comp]; exact e (.inl k)
  have a' : ∀ k, J (u.ex (z' k)).left = j' k := fun k => by
    rw [← hz' k, Category.id_comp]; exact e (.inr k)
  simpa only [frameProd, a, a'] using this

theorem eq_of_genVal (hL : L.IsLB) {t t' : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (ht' : t'.IsGen)
    {z : K → Fin g → ℂ} (hz : IsLift u φ (𝟙 _) z)
    (h : genVal u hL t (𝟙 _) z = genVal u hL t' (𝟙 _) z) : t = t' := by
  have : t.s = t'.s := funext fun j => Units.ext (fn_ext_val fun h₁ =>
    (valAt'_gen hL ht hz h₁).trans (Eq.trans (by rw [h]) (valAt'_gen hL ht' hz h₁).symm))
  obtain ⟨s⟩ := t
  obtain ⟨s'⟩ := t'
  exact congrArg LB.Gen.mk this

theorem exists_genVal (hL : L.IsLB) (ε : K → ℤ) {z : K → Fin g → ℂ} (hz : IsLift u φ (𝟙 _) z) {c : ℂ} (hc : c ≠ 0) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ genVal u hL t (𝟙 _) z = c := by
  choose s hs using fun j : K → L.ι => exists_unit_val (L.wchart φ j) (c * frameProd u ε z j)
    fun hj => mul_ne_zero hc (frameProd_ne_zero hz ε hj)
  refine ⟨⟨s⟩, fun j j' => Units.ext (fn_ext_val fun h₃ => ?_), ?_⟩
  · obtain ⟨hj, hj'⟩ := (le_preimage_inf _ _ _).1 h₃
    have e₂ := val_linComb (𝟙 _) valueRules L φ ε j j' hj hj'
    have e₃ : frameProd u ε z j = valAt' (𝟙 _) (L.wchart φ j ⊓ L.wchart φ j') ((L.LinComb φ ε).g j j').val *
        frameProd u ε z j' := by
      refine Eq.trans ?_ (congrArg (· * _) e₂).symm
      simp only [frameProd]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [u.fr_compat (j k) (j' k) (z k) ((le_preimage_inf _ _ _).2 ⟨(hz.le_iff j).1 hj k, (hz.le_iff j').1 hj' k⟩),
        mul_zpow, hz k]
    refine ((val_res _ valueRules inf_le_left h₃ _).trans (hs j hj)).trans (Eq.trans ?_
      ((val_unit_mul _ valueRules h₃ _ _).trans (congrArg (_ * ·)
        ((val_res _ valueRules inf_le_right h₃ _).trans (hs j' hj')))).symm)
    rw [e₃]
    exact mul_left_comm _ _ _
  · have h := le_wchart_chartAt hL φ (𝟙 _)
    exact (congrArg (· / _) (hs _ h)).trans (mul_div_cancel_right₀ _ (frameProd_ne_zero hz ε h))

end Gen

theorem exists_log {X : Type} [AddCommGroup X] [Module.Free ℤ X] (v : X → ℂ) (h₀ : ∀ x, v x ≠ 0)
    (h : ∀ x y, v (x + y) = v x * v y) : ∃ lam : X →+ ℂ, ∀ x, v x = eTwoPi (lam x) := by
  let w : X →+ Additive ℂˣ := AddMonoidHom.mk' (fun x => Additive.ofMul (Units.mk0 _ (h₀ x)))
    fun x y => congrArg Additive.ofMul (Units.ext (h x y))
  let e : ℂ →+ Additive ℂˣ := AddMonoidHom.mk' (fun x => Additive.ofMul (Units.mk0 (eTwoPi x) (Complex.exp_ne_zero _)))
    fun x y => congrArg Additive.ofMul (Units.ext (by simp [eTwoPi, mul_add, Complex.exp_add]))
  have he : Function.Surjective e.toIntLinearMap := fun a =>
    ⟨Complex.log a.toMul.val / (2 * Real.pi * Complex.I), congrArg Additive.ofMul (Units.ext (by
      show Complex.exp _ = _
      rw [mul_div_cancel₀ _ Complex.two_pi_I_ne_zero, Complex.exp_log a.toMul.ne_zero]
      rfl))⟩
  obtain ⟨l, hl⟩ := Module.projective_lifting_property e.toIntLinearMap w.toIntLinearMap he
  exact ⟨l.toAddMonoidHom, fun x => (congrArg (fun q => (Additive.toMul (q x)).val) hl).symm⟩

section Points

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

theorem TF_hom : (Out.TF (R := ℂ) ℂ).hom = 𝟙 (Sp ℂ) := by
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  exact Spec.map_id _

variable {D : Out.DegPre ℂ} {g : ℕ} (u : HolUnif D.P.A D.P.L g)

abbrev pt (z : Fin g → ℂ) : Out.TF (R := ℂ) ℂ ⟶ D.P.A := toUnit _ ≫ u.ex z

theorem toUnit_left {B : Over (Sp ℂ)} (x : 𝟙_ (Over (Sp ℂ)) ⟶ B) :
    (show Sp ℂ ⟶ _ from (toUnit (Out.TF (R := ℂ) ℂ) ≫ x).left) = x.left := by
  show (Out.TF (R := ℂ) ℂ).hom ≫ x.left = _
  rw [TF_hom]
  exact Category.id_comp _

variable {u} {ct : D.X →+ (Fin g → ℂ)}

theorem isLift_gt (hc : ∀ x, u.ex (ct x) = D.c x) (z : Fin g → ℂ) (x : D.X) :
    IsLift u (Y := Sp ℂ) (Out.DegPre.gtφ D ℂ (pt u z) x) (𝟙 _) ![ct x + z, ct x, z, 0] := fun k => by
  refine (Category.id_comp _).trans (Eq.trans ?_ (toUnit_left _))
  fin_cases k
  · refine congrArg (fun q => q.left) (?_ : padd D.P.A (toUnit _ ≫ D.c x) (pt u z) = pt u (ct x + z))
    rw [pt, pt, u.ex_add, hc, MonObj.comp_mul]
    rfl
  · exact congrArg (fun q => (toUnit (Out.TF (R := ℂ) ℂ) ≫ q).left) (hc x).symm
  · rfl
  · refine congrArg (fun q => (toUnit (Out.TF (R := ℂ) ℂ) ≫ q).left) (?_ : η[D.P.A] = u.ex 0)
    rw [ex_zero, Hom.one_def]; simp

theorem lift_left (hc : ∀ x, u.ex (ct x) = D.c x) (z : Fin g → ℂ) (x x' : D.X) :
    (show Sp ℂ ⟶ _ from (lift (Out.DegPre.cF D ℂ x) (lift (Out.DegPre.cF D ℂ x') (pt u z))).left) =
      (pt3 u ![ct x, ct x', z]).left := by
  have e : lift (Out.DegPre.cF D ℂ x) (lift (Out.DegPre.cF D ℂ x') (pt u z)) = toUnit _ ≫ pt3 u ![ct x, ct x', z] := by
    simp [pt3, comp_lift, hc]
  exact (congrArg (fun q => q.left) e).trans (toUnit_left _)

theorem isLift_mult (hc : ∀ x, u.ex (ct x) = D.c x) (z : Fin g → ℂ) (x x' : D.X) :
    IsLift u (Y := Sp ℂ) (Sum.elim (Out.DegPre.gtφ D ℂ (pt u z) (x + x'))
      (fun k => (lift (Out.DegPre.cF D ℂ x) (lift (Out.DegPre.cF D ℂ x') (pt u z))).left ≫ thφ D.P.A (x3 D.P.A) k))
      (𝟙 _) (Sum.elim ![ct (x + x') + z, ct (x + x'), z, 0] (cubeLift ![ct x, ct x', z])) := by
  rintro (k | k)
  · exact isLift_gt hc z _ k
  · exact (Category.id_comp _).trans ((congrArg (· ≫ _) (lift_left hc z x x')).trans (isLift_cube u _ k))

theorem isLift_mult' (hc : ∀ x, u.ex (ct x) = D.c x) (z : Fin g → ℂ) (x x' : D.X) :
    IsLift u (Y := Sp ℂ) (Sum.elim (Out.DegPre.gtφ D ℂ (pt u z) x) (Out.DegPre.gtφ D ℂ (pt u z) x'))
      (𝟙 _) (Sum.elim ![ct x + z, ct x, z, 0] ![ct x' + z, ct x', z, 0]) := by
  rintro (k | k)
  exacts [isLift_gt hc z _ k, isLift_gt hc z _ k]

theorem prod_mult (a b z : Fin g → ℂ) (f : (Fin g → ℂ) → ℂˣ) :
    ∏ k, f (Sum.elim ![a + b + z, a + b, z, 0] (cubeLift ![a, b, z]) k) ^ Sum.elim Out.DegPre.gtε thε k =
      ∏ k, f (Sum.elim ![a + z, a, z, 0] ![b + z, b, z, 0] k) ^ Sum.elim Out.DegPre.gtε Out.DegPre.gtε k := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  refine (congrArg (_ * ·) (prod_thK fun I => f (∑ i ∈ I, ![a, b, z] i))).trans ?_
  simp only [sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val, Fin.prod_univ_four, Out.DegPre.gtε,
    zpow_neg, zpow_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem genVal_mult {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) (hc : ∀ x, u.ex (ct x) = D.c x)
    (z : Fin g → ℂ) (x x' : D.X) (t : LB.Gen (LB.LinComb D.P.L (Out.DegPre.gtφ D ℂ (pt u z) (x + x')) Out.DegPre.gtε)) :
    genVal u D.P.isLB (Y := Sp ℂ) (LB.mulGen D.P.L _ _ _ _ t
      (Out.DegPre.cubAt D ℂ (Out.DegPre.cF D ℂ x) (Out.DegPre.cF D ℂ x') (pt u z))) (𝟙 _)
      (Sum.elim ![ct (x + x') + z, ct (x + x'), z, 0] (cubeLift ![ct x, ct x', z])) =
      genVal u D.P.isLB (Y := Sp ℂ) t (𝟙 _) ![ct (x + x') + z, ct (x + x'), z, 0] := by
  refine (genVal_mul D.P.isLB _ _ _ _).trans ((congrArg₂ (· * ·) rfl ?_).trans (_root_.mul_one _))
  refine (genVal_pull D.P.isLB _ _ _ _).trans ?_
  refine Eq.trans ?_ (genVal_cube_of_face D.P.isLB h D.cub.t D.cub.isGen (D.cub.face 0) ![ct x, ct x', z])
  exact congrArg (fun q => genVal u D.P.isLB (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t q (cubeLift ![ct x, ct x', z]))
    ((Category.id_comp _).trans (lift_left hc z x x'))

theorem mult_iff {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) (hc : ∀ x, u.ex (ct x) = D.c x)
    (z : Fin g → ℂ) (s : ∀ x, LB.Gen (LB.LinComb D.P.L (Out.DegPre.gtφ D ℂ (pt u z) x) Out.DegPre.gtε))
    (hs : ∀ x, (s x).IsGen) (x x' : D.X) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (s (x + x'))
      (Out.DegPre.cubAt D ℂ (Out.DegPre.cF D ℂ x) (Out.DegPre.cF D ℂ x') (pt u z)))
      (LB.mulGen D.P.L _ _ _ _ (s x) (s x')) ↔
    genVal u D.P.isLB (Y := Sp ℂ) (s (x + x')) (𝟙 _) ![ct (x + x') + z, ct (x + x'), z, 0] =
      genVal u D.P.isLB (Y := Sp ℂ) (s x) (𝟙 _) ![ct x + z, ct x, z, 0] *
        genVal u D.P.isLB (Y := Sp ℂ) (s x') (𝟙 _) ![ct x' + z, ct x', z, 0] := by
  have a := genVal_mult h hc z x x' (s (x + x'))
  have b : genVal u D.P.isLB (Y := Sp ℂ) (LB.mulGen D.P.L _ _ _ _ (s x) (s x')) (𝟙 _)
      (Sum.elim ![ct x + z, ct x, z, 0] ![ct x' + z, ct x', z, 0]) =
      genVal u D.P.isLB (Y := Sp ℂ) (s x) (𝟙 _) ![ct x + z, ct x, z, 0] *
        genVal u D.P.isLB (Y := Sp ℂ) (s x') (𝟙 _) ![ct x' + z, ct x', z, 0] := genVal_mul D.P.isLB _ _ _ _
  have p := prod_mult (ct x) (ct x') z
  rw [← map_add] at p
  have g₁ := DVR.mulGen_isGen _ _ _ _ _ _ _ (hs (x + x')) (DVR.pullGen_isGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
    D.cub.isGen (lift (Out.DegPre.cF D ℂ x) (lift (Out.DegPre.cF D ℂ x') (pt u z))).left)
  have g₂ := DVR.mulGen_isGen _ _ _ _ _ _ _ (hs x) (hs x')
  exact ⟨fun hm => a.symm.trans ((genVal_corr D.P.isLB hm (isLift_mult hc z x x') (isLift_mult' hc z x x') p).trans b),
    fun e => corr_of_genVal D.P.isLB g₁ g₂ (isLift_mult hc z x x') (isLift_mult' hc z x x') p
      (a.trans (e.trans b.symm))⟩

theorem eq_pt {b : Out.TF (R := ℂ) ℂ ⟶ D.P.A} {z : Fin g → ℂ} (hb : (show Sp ℂ ⟶ _ from b.left) = (u.ex z).left) :
    b = pt u z := Over.OverMorphism.ext (hb.trans (toUnit_left _).symm)

end Points

theorem points_eq_characters : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g : ℕ) (u : HolUnif D.P.A D.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (ct : D.X →+ (Fin g → ℂ)), u.IsAH Hm χ → u.IsRig D.rig → (∀ x, u.ex (ct x) = D.c x) → ∀ z : Fin g → ℂ, (∀ lam : D.X →+ ℂ, ∃! p : Out.GtPtF D ℂ, (show Sp ℂ ⟶ _ from p.b.left) = (u.ex z).left ∧ ∀ x, FrameValue.genVal u D.P.isLB (p.s x) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![ct x + z, ct x, z, 0] = eTwoPi (lam x)) ∧ ∀ p : Out.GtPtF D ℂ, (show Sp ℂ ⟶ _ from p.b.left) = (u.ex z).left → ∃ lam : D.X →+ ℂ, ∀ x, FrameValue.genVal u D.P.isLB (p.s x) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![ct x + z, ct x, z, 0] = eTwoPi (lam x) := by
  intro _ _ D g u Hm χ ct h _ hc z
  refine ⟨fun lam => ?_, ?_⟩
  · choose s hs hv using fun x => exists_genVal D.P.isLB Out.DegPre.gtε (isLift_gt hc z x)
      (c := eTwoPi (lam x)) (Complex.exp_ne_zero _)
    refine ⟨⟨pt u z, s, hs, ?_, fun x x' => ?_⟩, ⟨toUnit_left _, hv⟩, ?_⟩
    · refine corr_of_genVal D.P.isLB (hs 0) (fun i j => (map_one _).trans ?_) (isLift_gt hc z 0) (z' := PEmpty.elim)
        (fun k => k.elim) (fun f => ?_) ((hv 0).trans (Eq.trans ?_ (genVal_one D.P.isLB _ _).symm))
      · exact ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
      · simp [Fin.prod_univ_four, Out.DegPre.gtε]
      · simp [eTwoPi]
    · refine (mult_iff h hc z s hs x x').2 ((hv _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (hv x) (hv x')).symm))
      simp [eTwoPi, mul_add, Complex.exp_add]
    · rintro ⟨b, s', hs', h₀, hm⟩ ⟨hb, hv'⟩
      obtain rfl : b = pt u z := eq_pt hb
      obtain rfl : s' = s := funext fun x => eq_of_genVal D.P.isLB (hs' x) (hs x) (isLift_gt hc z x)
        ((hv' x).trans (hv x).symm)
      rfl
  · rintro ⟨b, s, hs, h₀, hm⟩ hb
    obtain rfl : b = pt u z := eq_pt hb
    exact exists_log _ (fun x => genVal_ne_zero D.P.isLB _ (isLift_gt hc z x))
      fun x x' => (mult_iff h hc z s hs x x').1 (hm x x')

end GlobalTheory.TorusExtChar
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_complexPoints_eq_characters : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g : ℕ) (u : HolUnif D.P.A D.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (ct : D.X →+ (Fin g → ℂ)), u.IsAH Hm χ → u.IsRig D.rig → (∀ x, u.ex (ct x) = D.c x) → ∀ z : Fin g → ℂ, (∀ lam : D.X →+ ℂ, ∃! p : Out.GtPtF D ℂ, (show Sp ℂ ⟶ _ from p.b.left) = (u.ex z).left ∧ ∀ x, FrameValue.genVal u D.P.isLB (p.s x) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![ct x + z, ct x, z, 0] = eTwoPi (lam x)) ∧ ∀ p : Out.GtPtF D ℂ, (show Sp ℂ ⟶ _ from p.b.left) = (u.ex z).left → ∃ lam : D.X →+ ℂ, ∀ x, FrameValue.genVal u D.P.isLB (p.s x) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![ct x + z, ct x, z, 0] = eTwoPi (lam x) := by
  first | exact @GlobalTheory.TorusExtChar.points_eq_characters | exact GlobalTheory.TorusExtChar.points_eq_characters | (intros; apply GlobalTheory.TorusExtChar.points_eq_characters <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.ArcModel

open FrameValue

section Lift

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_eq_iff (z w : Fin g → ℂ) : u.ex z = u.ex w ↔ z - w ∈ u.Λ := by
  rw [← u.ker]
  have e : u.ex z = u.ex (z - w) * u.ex w := by rw [← u.ex_add, sub_add_cancel]
  rw [e]
  exact mul_eq_right

theorem ex_zero' : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem

theorem lin_ext {F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : ∀ z, u.ex (F z) = u.ex (G z)) : F = G := by
  haveI := u.discrete
  have hc : Continuous fun z => (⟨F z - G z, (ex_eq_iff u _ _).1 (h z)⟩ : u.Λ) :=
    Continuous.subtype_mk (F.continuous_of_finiteDimensional.sub G.continuous_of_finiteDimensional) _
  refine LinearMap.ext fun z => ?_
  have := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := z) (y := 0))
  simpa [sub_eq_zero] using this

variable [IsCommMonObj A] {O : Type} [CommRing O]

theorem exists_ringHom_lift (r : Out.RingAct A O)
    (h : ∀ f : A ⟶ A, IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f) :
    ∃ F : O →+* Module.End ℂ (Fin g → ℂ), ∀ x z, u.ex (F x z) = u.ex z ≫ r.act x := by
  choose F hF using fun x => h (r.act x) (r.hom x)
  have add : ∀ a b, F (a + b) = F a + F b := fun a b => lin_ext u fun z => by
    rw [LinearMap.add_apply, u.ex_add, hF, hF, hF, r.map_add]
    exact MonObj.comp_mul _ _ _
  refine ⟨{ toFun := F, map_one' := lin_ext u fun z => ?_, map_mul' := fun a b => lin_ext u fun z => ?_,
            map_zero' := ?_, map_add' := add }, hF⟩
  · rw [hF, r.map_one, Category.comp_id]; rfl
  · rw [Module.End.mul_apply, hF, hF, hF, r.map_mul, Category.assoc]
  · simpa using add 0 0

theorem exists_lift_points (r : Out.RingAct A O) (F : O →+* Module.End ℂ (Fin g → ℂ))
    (hF : ∀ x z, u.ex (F x z) = u.ex z ≫ r.act x) {X : Type} [AddCommGroup X] [Module O X] [Module.Projective O X]
    (c : X → (𝟙_ (Over (Sp ℂ)) ⟶ A)) (hadd : ∀ a b, c (a + b) = padd A (c a) (c b))
    (hlin : ∀ (a : O) y, c (a • y) = c y ≫ r.act a) :
    ∃ ct : X →+ (Fin g → ℂ), (∀ (a : O) x, ct (a • x) = F a (ct x)) ∧ ∀ x, u.ex (ct x) = c x := by
  letI : Module O (Fin g → ℂ) := Module.compHom _ F
  have c0 : c 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact (mul_eq_left (a := c 0) (b := c 0)).1 this.symm
  let S : Submodule O (X × (Fin g → ℂ)) :=
    { carrier := {p | u.ex p.2 = c p.1}
      zero_mem' := (ex_zero' u).trans c0.symm
      add_mem' := fun {p q} hp hq => by
        change u.ex (p.2 + q.2) = c (p.1 + q.1)
        rw [u.ex_add, hadd, hp, hq]; rfl
      smul_mem' := fun a p hp => by
        change u.ex (F a p.2) = c (a • p.1)
        rw [hF, hlin, hp] }
  obtain ⟨s, hs⟩ := Module.projective_lifting_property ((LinearMap.fst O X _).comp S.subtype) LinearMap.id
    (fun x => by
      obtain ⟨z, hz⟩ := u.ex_onto (c x)
      exact ⟨⟨(x, z), hz⟩, rfl⟩)
  refine ⟨(((LinearMap.snd O X _).comp S.subtype).comp s).toAddMonoidHom, fun a x => ?_, fun x => ?_⟩
  · exact (((LinearMap.snd O X _).comp S.subtype).comp s).map_smul a x
  · exact (s x).2.trans (congrArg c (LinearMap.congr_fun hs x))

end Lift

section Values

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

theorem jFK_comp_point {B : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ B) :
    Out.jFK (R := ℂ) ℂ ≫ (toUnit (Out.TK ℂ) ≫ p).left = p.left := by
  change Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ ≫ p.left = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  exact (congrArg (· ≫ p.left) (Spec.map_id _)).trans (Category.id_comp _)

theorem jFK_comp_toUnit : Out.jFK (R := ℂ) ℂ ≫ (toUnit (Out.TK ℂ)).left = 𝟙 (Sp ℂ) := by
  simpa using jFK_comp_point (𝟙 (𝟙_ (Over (Sp ℂ))))

variable (D : Out.DegPre ℂ) {g : ℕ} (u : HolUnif D.P.A D.P.L g) (ct : D.X →+ (Fin g → ℂ))

def psiVal (x : D.X) : ℂ := genVal u D.P.isLB (D.psi x) (Out.jFK (R := ℂ) ℂ) (fun _ => ct x)

def tauVal (a b : D.X) : ℂ := psiVal D u ct (a + b) * (psiVal D u ct a)⁻¹ * (psiVal D u ct b)⁻¹

def tauLift (a b : D.X) : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit → Fin g → ℂ :=
  Sum.elim (Sum.elim (Sum.elim (fun _ => ct (a + b)) (fun _ => ct a)) (fun _ => ct b)) (fun _ => 0)

variable {D u ct}

theorem jFK_comp_xK (hc : ∀ x, u.ex (ct x) = D.c x) (x : D.X) :
    Out.jFK (R := ℂ) ℂ ≫ D.xK x = (u.ex (ct x)).left := by
  rw [hc]; exact jFK_comp_point _

theorem psiVal_ne_zero (hc : ∀ x, u.ex (ct x) = D.c x) (x : D.X) : psiVal D u ct x ≠ 0 :=
  genVal_ne_zero _ _ fun _ => jFK_comp_xK hc x

theorem genVal_tau (hr : u.IsRig D.rig) (a b : D.X) :
    genVal u D.P.isLB (D.tau a b) (Out.jFK (R := ℂ) ℂ) (tauLift D ct a b) = tauVal D u ct a b := by
  unfold Out.DegPre.tau Out.DegPre.rigK
  rw [genVal_mul, genVal_mul, genVal_mul, genVal_inv, genVal_inv, genVal_inv, genVal_pull, jFK_comp_toUnit]
  have := genVal_rig D.P.isLB hr
  erw [this]
  rw [inv_one, _root_.mul_one]
  rfl

theorem isLift_tau (hc : ∀ x, u.ex (ct x) = D.c x) (a b : D.X) :
    IsLift u (Sum.elim (Sum.elim (Sum.elim (fun _ : PUnit => D.xK (a + b)) (fun _ : PUnit => D.xK a))
      (fun _ : PUnit => D.xK b)) (fun _ : PUnit => (toUnit (Out.TK ℂ)).left ≫ eSec D.P.A))
      (Out.jFK (R := ℂ) ℂ) (tauLift D ct a b) := by
  rintro (((_ | _) | _) | _)
  · exact jFK_comp_xK hc _
  · exact jFK_comp_xK hc _
  · exact jFK_comp_xK hc _
  · change _ ≫ _ ≫ _ = (u.ex 0).left
    rw [← Category.assoc, jFK_comp_toUnit, ex_zero', Hom.one_def]
    simp [eSec]

variable {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem psiVal_neg (h : u.IsAH Hm χ) (hc : ∀ x, u.ex (ct x) = D.c x) (he : D.PsiEven) (x : D.X) :
    psiVal D u ct (-x) = psiVal D u ct x := by
  have e := genVal_corr (u := u) D.P.isLB (he x) (y := Out.jFK (R := ℂ) ℂ)
    (z := Sum.elim (fun _ => ct (-x)) ![-ct x, ct x]) (z' := fun _ => ct x)
    (by
      rintro (_ | k)
      · exact jFK_comp_xK hc _
      · change _ ≫ _ ≫ _ = _
        rw [← Category.assoc, jFK_comp_xK hc]
        exact isLift_sym u _ k)
    (fun _ => jFK_comp_xK hc x) (fun f => by simp [Fintype.prod_sum_type])
  rw [genVal_mul, genVal_pull, jFK_comp_xK hc] at e
  have s := (genVal_sym D.P.isLB h D.sym D.sym_gen D.sym_rig).1 (ct x)
  exact (_root_.mul_one _).symm.trans ((congrArg _ s.symm).trans e)

theorem tauVal_add (h : u.IsAH Hm χ) (hr : u.IsRig D.rig) (hc : ∀ x, u.ex (ct x) = D.c x) (hb : D.TauBimult)
    (a a' b : D.X) : tauVal D u ct (a + a') b = tauVal D u ct a b * tauVal D u ct a' b := by
  have hp : Out.jFK (R := ℂ) ℂ ≫ D.pt3 a a' b = (CubeValues.pt3 u ![ct a, ct a', ct b]).left := by
    rw [← jFK_comp_point]
    simp only [CubeValues.pt3, comp_lift, Out.DegPre.pt3, ← hc]
    rfl
  have e := genVal_corr (u := u) D.P.isLB (hb a a' b) (y := Out.jFK (R := ℂ) ℂ)
    (z := Sum.elim (tauLift D ct (a + a') b) (cubeLift ![ct a, ct a', ct b]))
    (z' := Sum.elim (tauLift D ct a b) (tauLift D ct a' b))
    (by
      rintro (k | k)
      · exact isLift_tau hc _ _ k
      · change _ ≫ _ ≫ _ = _
        rw [← Category.assoc, hp]
        exact isLift_cube u _ k)
    (by
      rintro (k | k)
      exacts [isLift_tau hc _ _ k, isLift_tau hc _ _ k])
    (fun f => by
      have := prod_thK (fun I => f (∑ i ∈ I, ![ct a, ct a', ct b] i))
      simp only [(sum_three _).1, (sum_three _).2.1, (sum_three _).2.2.1, (sum_three _).2.2.2] at this
      refine (Fintype.prod_sum_type _).trans ((congrArg (_ * ·) this).trans ?_)
      simp [tauLift, Fintype.prod_sum_type]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  replace e := (genVal_mul _ _ _ _ _).symm.trans (e.trans (genVal_mul _ _ _ _ _))
  have s := genVal_cube_of_face D.P.isLB h D.cub.t D.cub.isGen (D.cub.face 0) ![ct a, ct a', ct b]
  rw [← hp] at s
  replace s := (genVal_pull _ _ _ _ _).trans s
  rw [← genVal_tau hr, ← genVal_tau hr, ← genVal_tau hr]
  exact (_root_.mul_one _).symm.trans ((congrArg _ s.symm).trans e)

theorem tauVal_bal (hG : Out.GlobalFnsSt) (h : u.IsAH Hm χ) (hr : u.IsRig D.rig) (hc : ∀ x, u.ex (ct x) = D.c x)
    {f f' : D.P.A ⟶ D.P.A} [IsMonHom f] [IsMonHom f'] (hR : Out.RosatiAdj D.P.A D.P.L f f')
    {F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) (hF' : ∀ z, u.ex (G z) = u.ex z ≫ f')
    {a a' : D.X → D.X} (ha : ∀ x, ct (a x) = F (ct x)) (ha' : ∀ x, ct (a' x) = G (ct x)) (hb : D.TauBal f f' a a') :
    (∀ x z, hermForm Hm (F x) z = hermForm Hm x (G z)) ∧
      ∀ y y', tauVal D u ct (a y) y' = tauVal D u ct y (a' y') := by
  obtain ⟨r, hr₁, hr₀⟩ := exists_ros hG D.P.isAb D.P.isLB f f' hR
  obtain ⟨adj, s⟩ := genVal_rosati D.P.isLB h hF hF' r hr₁ hr₀
  refine ⟨adj, fun y y' => ?_⟩
  have hp : Out.jFK (R := ℂ) ℂ ≫ D.pt2 y y' = (lift (u.ex (ct y)) (u.ex (ct y'))).left := by
    rw [← jFK_comp_point]
    simp only [comp_lift, Out.DegPre.pt2, ← hc]
  have e := genVal_corr (u := u) D.P.isLB (hb r hr₁ hr₀ y y') (y := Out.jFK (R := ℂ) ℂ)
    (z := Sum.elim (tauLift D ct (a y) y') (rosatiLift F G (ct y) (ct y')))
    (z' := tauLift D ct y (a' y'))
    (by
      rintro (k | k)
      · exact isLift_tau hc _ _ k
      · change _ ≫ _ ≫ _ = _
        rw [← Category.assoc, hp]
        exact isLift_rosati hF hF' _ _ k)
    (isLift_tau hc _ _)
    (fun f => by
      simp [Fintype.prod_sum_type, tauLift, rosatiLift, Out.rosatiε, Fin.prod_univ_six, ha, ha']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  rw [genVal_mul, genVal_pull, hp] at e
  rw [← genVal_tau hr, ← genVal_tau hr]
  exact (_root_.mul_one _).symm.trans ((congrArg _ (s _ _).symm).trans e)

end Values

theorem nonempty_gtAn : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b),
    letI := H.starRing; Nonempty (GtAn a) := by
  intro hL _ hT E _ _ _ H D l c O _ β _ _ b a
  letI := H.starRing
  obtain ⟨u, Hm, χ, Ef, hAH, hrig, ht₁, ht₂, hend, hpow, hEf, hbij, -⟩ := hT a.D₀.P a.D₀.rig a.D₀.rig_gen
  obtain ⟨F, hF⟩ := exists_ringHom_lift u a.oa.onB.toRingAct hend
  haveI : Module.Projective (𝓞 E) a.D₀.X := Forms.projective_of_int _ _
  haveI : Module.Finite (𝓞 E) a.D₀.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨ct, hct, hc⟩ := exists_lift_points u a.oa.onB.toRingAct F hF a.D₀.c a.D₀.c_add a.oa.c_lin
  have bal := fun x : 𝓞 E =>
    haveI := a.oa.onB.hom x
    haveI := a.oa.onB.hom (star x)
    tauVal_bal hL.globalFns hAH hrig hc (a.oa.onB.rosati x) (hF x) (hF (star x)) (hct x) (hct (star x))
      (a.oa.tau_bal x)
  have ne := psiVal_ne_zero hc
  have symm : ∀ y x, tauVal a.D₀ u ct y x = tauVal a.D₀ u ct x y := fun y x => by
    rw [tauVal, tauVal, add_comm, mul_right_comm]
  have hw : H.w0 + star H.w0 = 1 := by
    change H.w0 + H.bar H.w0 = 1
    rw [HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]
  obtain ⟨T, T₁, T₂, T₃⟩ := Forms.exists_log_of_bimul_ne_zero hw (tauVal a.D₀ u ct)
    (fun y x => mul_ne_zero (mul_ne_zero (ne _) (inv_ne_zero (ne _))) (inv_ne_zero (ne _)))
    (fun y x x' => by rw [symm, tauVal_add hAH hrig hc a.bimult, symm x, symm x']) symm (fun x => (bal x).2)
  choose ex0 hex0 using fun v : (a.D₀.X →+ ℂ) × (Fin a.D₀.P.g → ℂ) =>
    ((GlobalTheory.T.torusExtension_complexPoints_eq_characters a.D₀ _ u Hm χ ct hAH hrig hc v.2).1 v.1).exists
  let A : AnArc (𝓞 E) :=
    { gB := a.D₀.P.g, abelian₂ := u.Λ, discrete := u.discrete, full := u.full, Hm := Hm, Hm_herm := hAH.1,
      Hm_pos := hAH.2.1, Ef := Ef, Ef_eq := hEf, Ef_bij := hbij, chi := χ, chi_norm := hAH.2.2.1,
      chi_add := chi_add a.D₀.P.isLB hAH,
      chi_neg := (genVal_sym a.D₀.P.isLB hAH a.D₀.sym a.D₀.sym_gen a.D₀.sym_rig).2,
      F := F, F_mem := fun x m hm => lift_mem (hF x) ⟨m, hm⟩, F_adj := fun x => (bal x).1,
      X := a.D₀.X, ct := ct, ct_smul := hct,
      T := LinearMap.toAddMonoidHom'.comp T.toAddMonoidHom, T_symm := T₁, T_adj := T₂,
      psi := fun x => Units.mk0 _ (ne x),
      psi_neg := fun x => Units.ext (psiVal_neg hAH hc a.even x),
      psi_add := fun x y => by
        change psiVal a.D₀ u ct (x + y) = psiVal a.D₀ u ct x * psiVal a.D₀ u ct y *
          Complex.exp (2 * Real.pi * Complex.I * T x y)
        rw [← T₃, tauVal]
        have := ne x
        have := ne y
        field_simp
      be := a.be, be_symm := a.be_symm, be_pos := a.be_pos, be_adj := a.be_adj,
      be_even := fun x => (dvd_mul_right _ _).trans (a.be_dvd x x) }
  exact ⟨{ star_eq := rfl, A := A, ε := LinearEquiv.refl _ _, be_eq := fun _ _ => rfl, gB_eq := rfl, u := u,
           lam := rfl, ah := hAH, rig := hrig, tan := ⟨ht₁, ht₂⟩, pow := hpow, act := hF, ct := hc,
           psi := fun _ => rfl, ex0 := ex0, ex0_b := fun v => (hex0 v).1, arcDict_expZero_section := fun v => (hex0 v).2 }⟩

end GlobalTheory.ArcModel
end
end
