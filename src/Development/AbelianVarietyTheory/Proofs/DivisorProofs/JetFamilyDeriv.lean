import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.VtfValPullGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DotProductMulVecEqTransposeMulVec

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.JetF

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}}

def vH (x : Sp F ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* F :=
  (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valF_eq (x : Sp F ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) : valF x U a = vH x U h a := by
  rw [valF, dif_pos h]; rfl

theorem valF_appLE {x : Sp F ⟶ X} {U : X.Opens} (f : X ⟶ Y) (W : Y.Opens) (e : U ≤ f ⁻¹ᵁ W)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Y, W)) : valF x U ((f.appLE W U e).hom a) = valF (x ≫ f) W a := by
  have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ W := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.appLE_comp_appLE x f W U ⊤ e h]
  rfl

theorem valF_res {x : Sp F ⟶ X} {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valF x V ((X.presheaf.map (homOfLE e).op).hom a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

theorem valF_unit_ne (x : Sp F ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) : valF x U a.val ≠ 0 := by
  rw [valF_eq x U h]
  exact (a.isUnit.map _).ne_zero

variable {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem mem_wchart {r : Sp F ⟶ Y} {j : K → L.ι} :
    ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (r ≫ φ k) ⁻¹ᵁ L.U (j k) :=
  ⟨fun h k _ hq => Set.mem_iInter.1 (h hq) k, fun h _ hq => Set.mem_iInter.2 fun k => h k hq⟩

theorem valF_sec (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) (j j' : K → L.ι)
    (h : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ j) (h' : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ j') :
    valF r (LB.wchart L φ j) (s.f j) =
      (∏ k, valF (r ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k) *
        valF r (LB.wchart L φ j') (s.f j') := by
  have h2 : ⊤ ≤ r ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := fun q hq => ⟨h hq, h' hq⟩
  have c := congrArg (vH r (LB.wchart L φ j ⊓ LB.wchart L φ j') h2) (s.compat j j')
  erw [map_mul] at c
  refine (valF_res inf_le_left h2 _).symm.trans ((valF_eq _ _ h2 _).trans (c.trans (congrArg₂ (· * ·) ?_
    ((valF_eq _ _ h2 _).symm.trans (valF_res inf_le_right h2 _)))))
  let ψ : Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ →* F :=
    (vH r (LB.wchart L φ j ⊓ LB.wchart L φ j') h2).toMonoidHom.comp (Units.coeHom _)
  change ψ (∏ k, _) = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  change (Units.coeHom F) ((Units.map (vH r (LB.wchart L φ j ⊓ LB.wchart L φ j') h2).toMonoidHom) _) = _
  rw [map_zpow, map_zpow]
  congr 1
  rw [← valF_appLE (φ k) _ (le_inf (inf_le_left.trans (LB.wchart_le L φ j k))
      (inf_le_right.trans (LB.wchart_le L φ j' k))) h2, valF_eq _ _ h2]
  rfl

end Val

section Jet
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def jet (W : E) (f : E → ℂ) (x : E) : DualNumber ℂ :=
  TrivSqZeroExt.inl (f x) + TrivSqZeroExt.inr (fderiv ℂ f x W)

theorem jet_mul (W : E) {f g : E → ℂ} {x : E} (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x) :
    jet W (fun z => f z * g z) x = jet W f x * jet W g x := by
  unfold jet
  rw [fderiv_fun_mul hf hg]
  ext <;> simp <;> ring

theorem jet_const (W : E) (c : ℂ) (x : E) : jet W (fun _ => c) x = TrivSqZeroExt.inl c := by
  simp [jet]

theorem jet_pow (W : E) {f : E → ℂ} {x : E} (hf : DifferentiableAt ℂ f x) (k : ℕ) :
    jet W (fun z => f z ^ k) x = jet W f x ^ k := by
  induction k with
  | zero => simp [jet_const]
  | succ k ih =>
    simp only [pow_succ]
    rw [jet_mul W (hf.fun_pow k) hf, ih]

theorem jet_congr (W : E) {f g : E → ℂ} {x : E} (h : f =ᶠ[nhds x] g) : jet W f x = jet W g x := by
  unfold jet
  rw [h.fderiv_eq, h.eq_of_nhds]

theorem jet_add (W : E) (f : E → ℂ) (c : E) : jet W (fun z => f (c + z)) 0 = jet W f c := by
  unfold jet
  rw [fderiv_comp_add_left]
  simp only [add_zero]

end Jet

section Main
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
  (ν : NumOf D ℂ N) (d : AB N.toNumB g)

theorem ex_zero : d.ex 0 = 1 := by
  have := d.ex_add 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem ptB_prB (z : Fin g → ℂ) : ptB ν d z ≫ (DegPre.prB D ℂ).left = (ν.eA (d.ex z)).left :=
  congrArg (·.left) (lift_snd (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z)))

theorem ptB_fam {α : N.X} {ct : Fin g → ℂ} (hc : N.c α = d.ex ct) (z : Fin g → ℂ) (k : Fin 4) :
    ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) k = (ν.eA (d.ex (![z, ct + z, ct, 0] k))).left := by
  have e2 : lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z)) ≫ toUnit _ ≫ D.c (ν.eX α) = ν.eA (d.ex ct) := by
    rw [← hc, ν.c_eq, ← Category.assoc, comp_toUnit]
  fin_cases k
  · exact ptB_prB ν d z
  · refine congrArg (·.left) (?_ : lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z)) ≫
      (DegPre.prB D ℂ * (toUnit _ ≫ D.c (ν.eX α))) = ν.eA (d.ex (ct + z)))
    rw [MonObj.comp_mul, e2, lift_snd, add_comm, d.ex_add, map_mul]
  · exact congrArg (·.left) e2
  · refine congrArg (·.left) (?_ : lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z)) ≫
      toUnit _ ≫ η[D.P.A] = ν.eA (d.ex 0))
    rw [ex_zero, map_one, ← Category.assoc, comp_toUnit]
    rfl

variable {ν d}

theorem open_chart (G : Geo ν d) (i : D.P.L.ι) : IsOpen {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ D.P.L.U i} := by
  have := (G.hol ((DegPre.prB D ℂ).left ⁻¹ᵁ D.P.L.U i) 0).1
  simp only [← ptB_prB]
  exact this

theorem frG_diff (G : Geo ν d) (x : Fin g → ℂ) : DifferentiableAt ℂ (G.frG (ν.J (ν.eA (d.ex x)).left)) x :=
  (G.fr_hol _).differentiableAt ((open_chart G _).mem_nhds (ν.good _))

theorem val_fam (G : Geo ν d) {k : ℕ} {s : Fam D ℂ k} {f : N.X → N.A → ℂ} {α : N.X} {ct : Fin g → ℂ} {φ : (Fin g → ℂ) → ℂ}
    (hs : ν.FamV s f) (hc : N.c α = d.ex ct)
    (hφ : ∀ z, f α (d.ex z) * d.fr ct * d.fr z = φ z * (d.fr z : ℂ) ^ k * d.fr (ct + z))
    (j : Fin 4 → D.P.L.ι) (z : Fin g → ℂ) (h : ⊤ ≤ ptB ν d z ⁻¹ᵁ LB.wchart D.P.L (DegPre.famφ D ℂ (ν.eX α)) j) :
    valF (ptB ν d z) (LB.wchart D.P.L (DegPre.famφ D ℂ (ν.eX α)) j) ((s.s (ν.eX α)).f j) * G.frG (j 2) ct * G.frG (j 0) z =
      φ z * G.frG (j 0) z ^ k * G.frG (j 1) (ct + z) * G.frG (j 3) 0 := by
  have h' : ⊤ ≤ ptB ν d z ⁻¹ᵁ LB.wchart D.P.L (DegPre.famφ D ℂ (ν.eX α))
      (fun k => ν.J (ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) k)) := mem_wchart.2 fun _ => ν.good _
  have e := valF_sec (s.s (ν.eX α)) (ptB ν d z) j _ h h'
  have e' : valF (ptB ν d z) _ ((s.s (ν.eX α)).f (fun k => ν.J (ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) k))) =
    f α (d.ex z) * ν.rg ^ k := (hs α (d.ex z)).symm
  have key : ∀ l : Fin 4, ∃ u : ℂ, u ≠ 0 ∧ valF (ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) l)
      (D.P.L.U (j l) ⊓ D.P.L.U (ν.J (ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) l)))
      (D.P.L.g (j l) (ν.J (ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) l))).val = u ∧
      G.frG (j l) (![z, ct + z, ct, 0] l) = u * (d.fr (![z, ct + z, ct, 0] l) * ν.rg) := fun l => by
    have h1 := mem_wchart.1 h l
    rw [ptB_fam ν d hc] at h1 ⊢
    have h2 : ⊤ ≤ (ν.eA (d.ex (![z, ct + z, ct, 0] l))).left ⁻¹ᵁ
        (D.P.L.U (j l) ⊓ D.P.L.U (ν.J (ν.eA (d.ex (![z, ct + z, ct, 0] l))).left)) :=
      fun q hq => ⟨h1 hq, ν.good _ hq⟩
    exact ⟨_, valF_unit_ne _ _ h2 _, rfl, by rw [G.fr_compat _ _ _ h2, G.fr_eq]⟩
  choose u hu0 hu1 hu2 using key
  have e3 := e.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun l _ => congrArg (· ^ DegPre.famε k l) (hu1 l)) e')
  rw [e3, Fin.prod_univ_four]
  have a0 : G.frG (j 0) z = u 0 * (d.fr z * ν.rg) := hu2 0
  have a1 : G.frG (j 1) (ct + z) = u 1 * (d.fr (ct + z) * ν.rg) := hu2 1
  have a2 : G.frG (j 2) ct = u 2 * (d.fr ct * ν.rg) := hu2 2
  have a3 : G.frG (j 3) 0 = u 3 * (d.fr 0 * ν.rg) := hu2 3
  rw [a0, a1, a2, a3, d.fr_zero]
  change u 0 ^ ((k : ℤ) - 1) * u 1 ^ (1 : ℤ) * u 2 ^ (-1 : ℤ) * u 3 ^ (1 : ℤ) * _ * _ * _ = _
  rw [zpow_sub₀ (hu0 0), zpow_natCast]
  simp only [zpow_one, _root_.zpow_neg, Units.val_one, mul_pow]
  rw [div_eq_mul_inv]
  linear_combination (u 0 ^ k * u 1 * u 3 * ν.rg ^ k * ν.rg ^ 2) * hφ z +
    (u 0 ^ k * u 1 * u 3 * ν.rg ^ k * ν.rg ^ 2) * (f α (d.ex z) * d.fr ct * d.fr z) *
      (u 2 * (u 2)⁻¹ * mul_inv_cancel₀ (hu0 0) + mul_inv_cancel₀ (hu0 2))

theorem red_eq (b : TE R ℂ ⟶ D.P.A) (hb : redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left) :
    redE ℂ ≫ (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left = ptB ν d 0 := by
  have h0 : redE ℂ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 1
  let ρ : TF (R := R) ℂ ⟶ TE R ℂ := Over.homMk (redE ℂ) (by
    change redE ℂ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ _ = _
    rw [← Category.assoc, h0, Category.id_comp])
  refine congrArg (·.left) (?_ : ρ ≫ lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b =
    lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex 0)))
  rw [comp_lift, ex_zero, map_one]
  congr 1
  · exact Over.OverMorphism.ext h0
  · exact Over.OverMorphism.ext hb

end Main

end GlobalTheory.MBLow.Cl.JetF

namespace GlobalTheory.MBLow.Cl
open JetF

theorem sE_fam_eq_jet : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g) (G : Geo ν d) (b : TE R ℂ ⟶ D.P.A) (W : Fin g → ℂ), redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left → IsD ν d W b → ∀ (k : ℕ) (s : Fam D ℂ k) (f : N.X → N.A → ℂ) (α : N.X) (ct : Fin g → ℂ) (φ : (Fin g → ℂ) → ℂ), ν.FamV s f → N.c α = d.ex ct → Differentiable ℂ φ → (∀ z, f α (d.ex z) * d.fr ct * d.fr z = φ z * (d.fr z : ℂ) ^ k * d.fr (ct + z)) → sE (s.s (ν.eX α)) (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left ν.J * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) = (TrivSqZeroExt.inl (φ 0) + TrivSqZeroExt.inr (fderiv ℂ φ 0 W)) * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) ^ k * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex ct)).left)) ct W) : DualNumber ℂ) * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) := by
  intro R _ _ _ _ D _ _ _ N ν g d G b W hb hD k s f α ct φ hs hc hφ hf
  let j : Fin 4 → D.P.L.ι := fun l => ν.J (ptB ν d 0 ≫ DegPre.famφ D ℂ (ν.eX α) l)
  have hU : ⊤ ≤ ptB ν d 0 ⁻¹ᵁ LB.wchart D.P.L (DegPre.famφ D ℂ (ν.eX α)) j := mem_wchart.2 fun _ => ν.good _
  have j0 : j 0 = ν.J (ν.eA (d.ex 0)).left := congrArg ν.J (ptB_fam ν d hc 0 0)
  have j1 : j 1 = ν.J (ν.eA (d.ex ct)).left := congrArg ν.J ((ptB_fam ν d hc 0 1).trans (by simp))
  have j2 : j 2 = ν.J (ν.eA (d.ex ct)).left := congrArg ν.J (ptB_fam ν d hc 0 2)
  have j3 : j 3 = ν.J (ν.eA (d.ex 0)).left := congrArg ν.J (ptB_fam ν d hc 0 3)
  let h : (Fin g → ℂ) → ℂ := fun z =>
    valF (ptB ν d z) (LB.wchart D.P.L (DegPre.famφ D ℂ (ν.eX α)) j) ((s.s (ν.eX α)).f j)
  have e1 : sE (s.s (ν.eX α)) (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl :
      TE R ℂ ⟶ TF (R := R) ℂ) b).left ν.J = jet W h 0 := by
    have ej : (fun l => ν.J (redE ℂ ≫ (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl :
        TE R ℂ ⟶ TF (R := R) ℂ) b).left ≫ DegPre.famφ D ℂ (ν.eX α) l)) = j := funext fun l =>
      congrArg ν.J ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (red_eq b hb)))
    unfold sE
    rw [ej]
    exact hD _ _ hU
  obtain ⟨ho, hd⟩ := G.hol _ ((s.s (ν.eX α)).f j)
  have hn := ho.mem_nhds hU
  have hh : DifferentiableAt ℂ h 0 := hd.differentiableAt hn
  have d0 := frG_diff G 0
  have dc : DifferentiableAt ℂ (fun z => G.frG (ν.J (ν.eA (d.ex ct)).left) (ct + z)) 0 := by
    refine DifferentiableAt.comp (g := G.frG (ν.J (ν.eA (d.ex ct)).left)) (f := fun z => ct + z) 0 ?_ (by fun_prop)
    rw [add_zero]
    exact frG_diff G ct
  have ev : (fun z => h z * G.frG (ν.J (ν.eA (d.ex ct)).left) ct * G.frG (ν.J (ν.eA (d.ex 0)).left) z) =ᶠ[nhds 0]
      fun z => φ z * G.frG (ν.J (ν.eA (d.ex 0)).left) z ^ k * G.frG (ν.J (ν.eA (d.ex ct)).left) (ct + z) *
        G.frG (ν.J (ν.eA (d.ex 0)).left) 0 := by
    filter_upwards [hn] with z hz
    have := val_fam G hs hc hf j z hz
    rwa [j0, j1, j2, j3] at this
  have := jet_congr W ev
  rw [jet_mul W (hh.mul_const _) d0, jet_mul W hh (differentiableAt_const _), jet_const,
    jet_mul W (((hφ 0).fun_mul (d0.fun_pow k)).fun_mul dc) (differentiableAt_const _), jet_const,
    jet_mul W ((hφ 0).fun_mul (d0.fun_pow k)) dc, jet_mul W (hφ 0) (d0.fun_pow k), jet_pow W d0, jet_add] at this
  rw [e1]
  exact this

end GlobalTheory.MBLow.Cl

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyMember_tangentValue_eq_firstJet : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g) (G : Geo ν d) (b : TE R ℂ ⟶ D.P.A) (W : Fin g → ℂ), redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left → IsD ν d W b → ∀ (k : ℕ) (s : Fam D ℂ k) (f : N.X → N.A → ℂ) (α : N.X) (ct : Fin g → ℂ) (φ : (Fin g → ℂ) → ℂ), ν.FamV s f → N.c α = d.ex ct → Differentiable ℂ φ → (∀ z, f α (d.ex z) * d.fr ct * d.fr z = φ z * (d.fr z : ℂ) ^ k * d.fr (ct + z)) → sE (s.s (ν.eX α)) (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left ν.J * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) = (TrivSqZeroExt.inl (φ 0) + TrivSqZeroExt.inr (fderiv ℂ φ 0 W)) * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) ^ k * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex ct)).left)) ct W) : DualNumber ℂ) * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) := by
  atlas_forward_decl GlobalTheory.MBLow.Cl.sE_fam_eq_jet
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
noncomputable section
namespace GlobalTheory.MBLow.Cl

theorem fst_vE_eq_one : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    (ν : NumOf D ℂ N) (gm : GtPt D (TE R ℂ)), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → ∀ (χ : D.X),
    (vE (gm.s χ) (𝟙 _) ν.J).fst = 1 := by
  intro R _ _ D _ N ν gm ⟨o, hz, hp⟩ χ
  have hJ : Good D.P.L (IsLocalRing.closedPoint ℂ) ν.J := fun ψ => ν.good ψ trivial
  have hm : redE ℂ (IsLocalRing.closedPoint ℂ) ∈ LB.wchart D.P.L (DegPre.gtφT D (TE R ℂ) gm.b χ)
      (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)) := by
    simpa only [Category.id_comp] using hJ.mem (DegPre.gtφT D (TE R ℂ) gm.b χ) (redE ℂ)
  have h : ⊤ ≤ (𝟙 (Sp (DualNumber ℂ))) ⁻¹ᵁ LB.wchart D.P.L (DegPre.gtφT D (TE R ℂ) gm.b χ)
      (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)) := by
    refine (GlobalTheory.KS.TangentAt.top_le_iff_dual _ _).2 ((GlobalTheory.ZH.CrdCalc.top_le_iff _ _).2 ?_)
    rw [Category.comp_id]
    exact hm
  have e1 : valR (redE ℂ ≫ 𝟙 (Sp (DualNumber ℂ))) (LB.wchart D.P.L (DegPre.gtφT D (TE R ℂ) gm.b χ)
      (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)))
      ((gm.s χ).s fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)).val = (vE (gm.s χ) (𝟙 _) ν.J).fst :=
    (GlobalTheory.ZH.CrdCalc.valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (𝟙 _) _ h).2 _
  rw [Category.comp_id] at e1
  have e2 := GlobalTheory.ZH.ThetaData.valR_eq_gs (redE ℂ) _ hm
    ((gm.s χ).s fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)).val
  have e3 := gs_unit (redE ℂ) (IsLocalRing.closedPoint ℂ) _ hm
    ((gm.s χ).s fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k))
  have e4 := val_of (gm.s χ) (redE ℂ) (IsLocalRing.closedPoint ℂ) ν.J
    (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)) (fun k => by rw [Category.id_comp])
  have v1 := val_pull hJ (gm.s χ) (redE ℂ) (𝟙 _)
  rw [Category.id_comp] at v1
  have v2 := (val_corr hJ (hp.2 χ) (𝟙 _)).symm.trans ((val_corr hJ (hz.2 χ) (𝟙 _)).trans (val_one _))
  rw [v1] at v2
  refine e1.symm.trans (e2.trans ?_)
  rw [e3, ← e4, v2, Units.val_one, map_one]

end GlobalTheory.MBLow.Cl
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_characterValue_constantTerm_one : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    (ν : NumOf D ℂ N) (gm : GtPt D (TE R ℂ)), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → ∀ (χ : D.X),
    (vE (gm.s χ) (𝟙 _) ν.J).fst = 1 := by
  atlas_forward_decl GlobalTheory.MBLow.Cl.fst_vE_eq_one
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.DualMult

theorem redE_closedPoint :
    (redE ℂ) (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint (DualNumber ℂ) := by
  have hl : IsLocalHom (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).hom :=
    ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
  exact Spec_closedPoint (f := CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)

variable {X : Scheme.{0}} {L : LB X}

theorem good_dual (J : (Sp ℂ ⟶ X) → L.ι) (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) :
    Good L (IsLocalRing.closedPoint (DualNumber ℂ) : Sp (DualNumber ℂ)) (fun ψ => J (redE ℂ ≫ ψ)) := by
  intro ψ
  have h := hJ (redE ℂ ≫ ψ) (x := IsLocalRing.closedPoint ℂ) trivial
  change ψ ((redE ℂ) (IsLocalRing.closedPoint ℂ)) ∈ L.U (J (redE ℂ ≫ ψ)) at h
  rwa [redE_closedPoint] at h

theorem vE_eq_val (J : (Sp ℂ ⟶ X) → L.ι) (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {K : Type} [Fintype K]
    {φ : K → (Sp (DualNumber ℂ) ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) :
    vE t (𝟙 _) J = (stalkClosedPointIso (CommRingCat.of (DualNumber ℂ))).hom.hom
      (val t (𝟙 _) (IsLocalRing.closedPoint (DualNumber ℂ) : Sp (DualNumber ℂ)) (fun ψ => J (redE ℂ ≫ ψ))).val := by
  have hm := (good_dual J hJ).mem φ (𝟙 _)
  unfold vE val
  exact (GlobalTheory.ZH.ThetaData.valR_eq_gs _ _ hm _).trans (congrArg _ (gs_unit _ _ _ hm _))

end GlobalTheory.DualMult

namespace GlobalTheory.DualMult
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}

theorem mult_vE (ν : NumOf D ℂ N) (gm : GtPt D (TE R ℂ)) (χ χ' : D.X) :
    vE (gm.s (χ + χ')) (𝟙 _) ν.J *
        vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
      vE (gm.s χ) (𝟙 _) ν.J * vE (gm.s χ') (𝟙 _) ν.J := by
  have hJ := good_dual (L := D.P.L) ν.J ν.good
  have e := val_corr hJ (gm.mult χ χ') (𝟙 _)
  replace e := (val_mul hJ _ _ _).symm.trans (e.trans (val_mul hJ _ _ _))
  refine (congrArg₂ (· * ·) (vE_eq_val ν.J ν.good _) (vE_eq_val ν.J ν.good _)).trans
    (Eq.trans ?_ (congrArg₂ (· * ·) (vE_eq_val ν.J ν.good _) (vE_eq_val ν.J ν.good _)).symm)
  rw [← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul]
  exact congrArg (fun u => (stalkClosedPointIso (CommRingCat.of (DualNumber ℂ))).hom.hom (Units.val u)) e

end GlobalTheory.DualMult
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_dualCharValues_mul_cube : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    (ν : NumOf D ℂ N) (gm : GtPt D (TE R ℂ)) (χ χ' : D.X),
    vE (gm.s (χ + χ')) (𝟙 _) ν.J *
        vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
      vE (gm.s χ) (𝟙 _) ν.J * vE (gm.s χ') (𝟙 _) ν.J := by
  atlas_forward_decl GlobalTheory.DualMult.mult_vE
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.SymFrame
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem const_of_periodic {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef)
    {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f) (hper : ∀ z M N, f (z + perV τ M N) = f z) (z w : Fin g → ℂ) :
    f z = f w := by
  let P : (Fin g → ℤ) × (Fin g → ℤ) →+ (Fin g → ℂ) := AddMonoidHom.mk' (fun a => perV τ a.1 a.2) fun a b => by
    have e : ∀ M N : Fin g → ℤ, cv (M + N) = cv M + cv N := fun M N => by ext i; simp [cv]
    simp only [perV, Prod.fst_add, Prod.snd_add, e, Matrix.mulVec_add]
    abel
  refine periodic_const_range P (eq_top_iff.2 fun v _ => ?_) f hf (fun z a => hper z a.1 a.2) z w
  obtain ⟨y, hy⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hp.isUnit fun i => (v i).im
  let x : Fin g → ℝ := fun i => (v i).re - (τ.map Complex.re *ᵥ y) i
  have e : v = ∑ i, x i • P (Pi.single i 1, 0) + ∑ i, y i • P (0, Pi.single i 1) := by
    have c0 : cv (0 : Fin g → ℤ) = 0 := by ext i; simp [cv]
    have c1 : ∀ i : Fin g, cv (Pi.single i 1 : Fin g → ℤ) = Pi.single i 1 := fun i => by
      ext k; by_cases h : k = i <;> simp [cv, h, Pi.single_apply]
    ext k
    have hk := congrFun hy k
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hk
    simp only [P, AddMonoidHom.mk'_apply, perV, c0, c1, Matrix.mulVec_zero, add_zero, zero_add, Matrix.mulVec_single_one,
      Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    apply Complex.ext
    · simp [x, Matrix.mulVec, dotProduct, mul_comm]
    · simp [← hk, mul_comm]
  rw [e]
  exact Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

theorem autV_mul_autV {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) {a b : Fin g → ℂ} (ha : Half a) (hb : Half b)
    (M N : Fin g → ℤ) (z : Fin g → ℂ) : autV τ a b M N z * autV τ a b M N (-(z + perV τ M N)) = 1 := by
  have h : ∀ {c : Fin g → ℂ}, Half c → ∀ M : Fin g → ℤ, ∃ n : ℤ, 2 * (c ⬝ᵥ cv M) = n := fun {c} hc M => by
    classical
    refine ⟨∑ i, if c i = 0 then 0 else M i, ?_⟩
    rw [dotProduct, Finset.mul_sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hc i with e | e <;> simp [e, cv]
  obtain ⟨m, hm⟩ := h ha M
  obtain ⟨n, hn⟩ := h hb N
  have hk : cv N ⬝ᵥ cv M = ((N ⬝ᵥ M : ℤ) : ℂ) := by simp [dotProduct, cv]
  rw [autV, autV, ← Complex.exp_add, Complex.exp_eq_one_iff]
  refine ⟨m - n + N ⬝ᵥ M, ?_⟩
  rw [dotProduct_neg, dotProduct_add, perV, dotProduct_add, hk]
  push_cast
  rw [← hm, ← hn]
  ring

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
  {ν : NumOf D ℂ N} {d : AB N.toNumB g}

theorem hol_base (G : Geo ν d) (U : D.P.A.left.Opens) (f : Γ(D.P.A.left, U)ˣ) :
    IsOpen {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valF (ν.eA (d.ex z)).left U f.val) {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ U} := by
  have e : ∀ z, ptB ν d z ≫ (snd (TF (R := R) ℂ) D.P.A).left = (ν.eA (d.ex z)).left := fun z => by
    rw [ptB, ← Over.comp_left, lift_snd]
  have h := G.hol ((snd (TF (R := R) ℂ) D.P.A).left ⁻¹ᵁ U) (pullU _ U f).val
  simp only [← e]
  refine ⟨h.1, h.2.congr fun z _ => ?_⟩
  exact (vtf_val_pullU (ptB ν d z) _ U f).symm

theorem differentiable_gen (G : Geo ν d) (hr : ν.rg ≠ 0) {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε)) (ht : t.IsGen) (w : K → (Fin g → ℂ) → (Fin g → ℂ))
    (hw : ∀ k, Differentiable ℂ (w k)) (hφ : ∀ k z, (ν.eA (d.ex z)).left ≫ φ k = (ν.eA (d.ex (w k z))).left) :
    Differentiable ℂ fun z => vF t (ν.eA (d.ex z)).left ν.J / ∏ k, ((d.fr (w k z) : ℂ) * ν.rg) ^ ε k := by
  intro z₀
  let j : K → D.P.L.ι := fun k => ν.J ((ν.eA (d.ex z₀)).left ≫ φ k)
  obtain ⟨hS, hv⟩ := hol_base G (LB.wchart D.P.L φ j) (t.s j)
  have hJ : ∀ z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ LB.wchart D.P.L φ fun k => ν.J ((ν.eA (d.ex z)).left ≫ φ k) :=
    fun z q _ => Set.mem_iInter.2 fun k => ν.good ((ν.eA (d.ex z)).left ≫ φ k) (x := q) trivial
  have hk : ∀ z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ LB.wchart D.P.L φ j → ∀ k,
      ⊤ ≤ (ν.eA (d.ex (w k z))).left ⁻¹ᵁ D.P.L.U (j k) := fun z hz k q _ => by
    rw [← hφ]
    exact Set.mem_iInter.1 (hz (x := q) trivial) k
  have hfr : ∀ z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ LB.wchart D.P.L φ j → ∀ k, (d.fr (w k z) : ℂ) * ν.rg =
      valF ((ν.eA (d.ex z)).left ≫ φ k) _ (D.P.L.g (ν.J ((ν.eA (d.ex z)).left ≫ φ k)) (j k)).val * G.frG (j k) (w k z) :=
    fun z hz k => by
      rw [hφ, G.fr_eq]
      exact G.fr_compat _ _ _ fun q _ => ⟨ν.good _ (x := q) trivial, hk z hz k (x := q) trivial⟩
  have hne : ∀ k z, (d.fr (w k z) : ℂ) * ν.rg ≠ 0 := fun k z => mul_ne_zero (Units.ne_zero _) hr
  have hev : (fun z => vF t (ν.eA (d.ex z)).left ν.J / ∏ k, ((d.fr (w k z) : ℂ) * ν.rg) ^ ε k) =ᶠ[nhds z₀]
      fun z => valF (ν.eA (d.ex z)).left (LB.wchart D.P.L φ j) (t.s j).val / ∏ k, G.frG (j k) (w k z) ^ ε k := by
    filter_upwards [hS.mem_nhds (hJ z₀)] with z hz
    have e : vF t (ν.eA (d.ex z)).left ν.J = (∏ k, valF ((ν.eA (d.ex z)).left ≫ φ k) _
        (D.P.L.g (ν.J ((ν.eA (d.ex z)).left ≫ φ k)) (j k)).val ^ ε k) *
        valF (ν.eA (d.ex z)).left (LB.wchart D.P.L φ j) (t.s j).val :=
      vtf_isGen_val D.P.L φ ε t ht _ _ j fun q _ => ⟨hJ z (x := q) trivial, hz (x := q) trivial⟩
    rw [e]
    simp only [hfr z hz, mul_zpow, Finset.prod_mul_distrib]
    refine mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ ?_)
    exact left_ne_zero_of_mul (hfr z hz k ▸ hne k z)
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have h0 : ∀ k, G.frG (j k) (w k z₀) ≠ 0 := fun k => right_ne_zero_of_mul (hfr z₀ (hJ z₀) k ▸ hne k z₀)
  have h1 : ∀ k, DifferentiableAt ℂ (fun z => G.frG (j k) (w k z)) z₀ := fun k =>
    ((G.fr_hol (j k)).differentiableAt ((hol_base G _ 1).1.mem_nhds (hk z₀ (hJ z₀) k))).comp z₀ (hw k z₀)
  have h2 : DifferentiableAt ℂ (fun z => ∏ k, G.frG (j k) (w k z) ^ ε k) z₀ :=
    by
      have hp : ∀ s : Finset K, DifferentiableAt ℂ (fun z => ∏ k ∈ s, G.frG (j k) (w k z) ^ ε k) z₀ := fun s => by
        classical
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          simp only [Finset.prod_insert ha]
          exact ((h1 a).zpow (Or.inl (h0 a))).mul ih
      exact hp _
  simp only [div_eq_mul_inv]
  exact (hv.differentiableAt (hS.mem_nhds (hJ z₀))).mul
    (h2.inv (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h0 k)))

theorem rg_ne (ν : NumOf D ℂ N) : ν.rg ≠ 0 := by
  unfold NumOf.rg vF valF
  split_ifs with h
  · exact (((Units.isUnit _).map _).map _).ne_zero
  · exact (h fun q _ => Set.mem_iInter.2 fun _ => ν.good ((TF (R := R) ℂ).hom ≫ eSec D.P.A) (x := q) trivial).elim

end GlobalTheory.MBLow.Cl.SymFrame

namespace GlobalTheory.MBLow.Cl
open SymFrame

theorem sym_of_geo : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), Nonempty (Geo ν d) → d.Sym := by
  rintro R _ _ _ _ D - - _ N ν g d ⟨G⟩
  have hr := rg_ne ν
  have h0 : d.ex 0 = 1 := by simpa using d.ex_add 0 0
  have hneg : ∀ z, d.ex (-z) = (d.ex z)⁻¹ := fun z =>
    eq_inv_of_mul_eq_one_left (by rw [← d.ex_add, neg_add_cancel, h0])
  have hd := differentiable_gen G hr D.sym D.sym_gen ![fun z => -z, fun z => z]
    (fun k => by fin_cases k <;> simp <;> fun_prop) (fun k z => by
      fin_cases k
      · change _ ≫ (ι[D.P.A]).left = (ν.eA (d.ex (-z))).left
        rw [hneg, map_inv, Hom.inv_def, Over.comp_left]
      · exact Category.comp_id _)
  have hF : Differentiable ℂ fun z => (N.σ (d.ex z) : ℂ) * d.fr z / d.fr (-z) := by
    convert hd using 2 with z
    rw [ν.σ_eq, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, _root_.zpow_neg]
    have := (d.fr z).ne_zero
    have := (d.fr (-z)).ne_zero
    field_simp
  intro x
  have hc := const_of_periodic d.pos hF (fun z M M' => by
    have h1 := d.fr_per M M' z
    have h2 := d.fr_per M M' (-(z + perV d.τ M M'))
    have h3 := autV_mul_autV d.τ d.ha d.hb M M' z
    rw [show -(z + perV d.τ M M') + perV d.τ M M' = -z by abel] at h2
    rw [d.ex_add, (d.ker _).2 ⟨M, M', rfl⟩, _root_.mul_one, div_eq_div_iff (Units.ne_zero _) (Units.ne_zero _), h1, h2]
    linear_combination (-(N.σ (d.ex z) : ℂ) * d.fr (z + perV d.τ M M') * d.fr (-z)) * h3) x 0
  rw [h0, N.σ_one, neg_zero, d.fr_zero, div_eq_iff (Units.ne_zero _)] at hc
  ext
  simpa using hc

end GlobalTheory.MBLow.Cl

end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.MBLow.Cl.CubeVal

theorem prod_three' {M : Type} [CommMonoid M] (F : Finset (Fin 3) → M) :
    ∏ s, F s = F ∅ * F {0} * F {1} * F {2} * F {0, 1} * F {0, 2} * F {1, 2} * F {0, 1, 2} := by
  rw [show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  ac_rfl

theorem prod_three {M : Type} [CommMonoid M] (F : thK.{0} → M) :
    ∏ I, F I = F ⟨∅⟩ * F ⟨{0}⟩ * F ⟨{1}⟩ * F ⟨{2}⟩ * F ⟨{0, 1}⟩ * F ⟨{0, 2}⟩ * F ⟨{1, 2}⟩ * F ⟨{0, 1, 2}⟩ :=
  (Equiv.prod_comp (Equiv.ulift.symm : Finset (Fin 3) ≃ thK.{0}) F).symm.trans (prod_three' fun s => F ⟨s⟩)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem ex_sum (d : AB N.toNumB g) {κ : Type} (s : Finset κ) (v : κ → Fin g → ℂ) :
    d.ex (∑ i ∈ s, v i) = ∏ i ∈ s, d.ex (v i) := by
  classical
  have h0 : d.ex 0 = 1 := by
    have e := d.ex_add 0 0
    rw [add_zero] at e
    exact (mul_eq_left.1 e.symm)
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, d.ex_add, ih]

theorem pt_thφ (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) (I : thK.{0}) :
    (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left ≫ thφ D.P.A (x3 D.P.A) I =
      (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left := by
  show _ ≫ (psum D.P.A (x3 D.P.A) I.down).left = _
  rw [← Over.comp_left, CubePf.CubeCoordinateSums.psum_eq_prod, CubePf.CubeCoordinateSums.comp_prod, ex_sum, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  fin_cases i <;> simp [x3]

end GlobalTheory.MBLow.Cl.CubeVal

namespace GlobalTheory.MBLow.Cl.CubeVal

theorem thε_vals : thε ⟨(∅ : Finset (Fin 3))⟩ = -1 ∧ thε ⟨({0} : Finset (Fin 3))⟩ = 1 ∧ thε ⟨({1} : Finset (Fin 3))⟩ = 1 ∧
    thε ⟨({2} : Finset (Fin 3))⟩ = 1 ∧ thε ⟨({0, 1} : Finset (Fin 3))⟩ = -1 ∧ thε ⟨({0, 2} : Finset (Fin 3))⟩ = -1 ∧
    thε ⟨({1, 2} : Finset (Fin 3))⟩ = -1 ∧ thε ⟨({0, 1, 2} : Finset (Fin 3))⟩ = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem prod_const_zpow (r : ℂ) (hr : r ≠ 0) : ∏ I : thK.{0}, r ^ thε I = 1 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := thε_vals
  rw [prod_three, e0, e1, e2, e3, e4, e5, e6, e7]
  field_simp

theorem alg (a b f : thK.{0} → ℂ) (r θ V : ℂ) (hr : r ≠ 0) (hf : ∀ I, f I ≠ 0) (h : ∀ I, f I * r = a I * b I)
    (h1 : θ = (∏ I, a I ^ thε I) * V) (h2 : θ = ∏ I, f I ^ thε I) : V = ∏ I, b I ^ thε I := by
  have ha : ∀ I, a I ≠ 0 := fun I => left_ne_zero_of_mul (h I ▸ mul_ne_zero (hf I) hr)
  have hA : (∏ I, a I ^ thε I) ≠ 0 := Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (ha I)
  have hAB : (∏ I, a I ^ thε I) * ∏ I, b I ^ thε I = ∏ I, f I ^ thε I := by
    rw [← Finset.prod_mul_distrib]
    have e : ∀ I, a I ^ thε I * b I ^ thε I = f I ^ thε I * r ^ thε I := fun I => by
      rw [← mul_zpow, ← mul_zpow, h I]
    simp only [e, Finset.prod_mul_distrib, prod_const_zpow r hr, _root_.mul_one]
  rw [h1] at h2
  exact mul_left_cancel₀ hA (h2.trans hAB.symm)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem theta_eq_prod (d : AB N.toNumB g) (hc : d.Cub) (x y z : Fin g → ℂ) :
    (N.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) = ∏ I : thK.{0}, (d.fr (∑ i ∈ I.down, ![x, y, z] i) : ℂ) ^ thε I := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := thε_vals
  have h := congrArg Units.val (hc x y z)
  simp only [Units.val_mul] at h
  rw [prod_three, e0, e1, e2, e3, e4, e5, e6, e7]
  simp [Finset.sum_insert, d.fr_zero, ← add_assoc]
  have := (d.fr (x + y)).ne_zero
  have := (d.fr (x + z)).ne_zero
  have := (d.fr (y + z)).ne_zero
  field_simp
  linear_combination h

end GlobalTheory.MBLow.Cl.CubeVal

namespace GlobalTheory.MBLow.Cl

open CubeVal in

theorem cube_val_frame : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g), d.Cub → ∀ (G : Geo ν d) (x y z : Fin g → ℂ) (j : thK.{0} → D.P.L.ι),
    (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ D.P.L.U (j I)) →
    valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
      (D.cub.t.s j).val = ∏ I : thK.{0}, G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I := by
  intro R _ _ D _ N g ν d hc G x y z j hj
  have hpt := pt_thφ ν d x y z
  set p := (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left with hp
  have htr : ∀ I : thK.{0}, (d.fr (∑ i ∈ I.down, ![x, y, z] i) : ℂ) * ν.rg =
      valF (p ≫ thφ D.P.A (x3 D.P.A) I) (D.P.L.U (ν.J (p ≫ thφ D.P.A (x3 D.P.A) I)) ⊓ D.P.L.U (j I))
        (D.P.L.g (ν.J (p ≫ thφ D.P.A (x3 D.P.A) I)) (j I)).val * G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) := by
    intro I
    rw [hpt I, G.fr_eq]
    exact G.fr_compat _ _ _ fun q _ => ⟨ν.good _ (x := q) trivial, hj I (x := q) trivial⟩
  have hin : ⊤ ≤ p ⁻¹ᵁ (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) (fun I => ν.J (p ≫ thφ D.P.A (x3 D.P.A) I)) ⊓
      LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j) := fun q _ =>
    ⟨Set.mem_iInter.2 fun I => ν.good (p ≫ thφ D.P.A (x3 D.P.A) I) (x := q) trivial,
      Set.mem_iInter.2 fun I => by
        have h := hj I
        rw [← hpt I] at h
        exact h (x := q) trivial⟩
  have e1 := PullbackSections.vtf_isGen_val D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t D.cub.isGen p _ j hin
  have e2 := ν.θ_eq (d.ex x) (d.ex y) (d.ex z)
  exact alg _ _ (fun I => (d.fr (∑ i ∈ I.down, ![x, y, z] i) : ℂ)) ν.rg _ _ (SymFrame.rg_ne ν) (fun I => Units.ne_zero _)
    htr (e2.trans e1) (theta_eq_prod d hc x y z)

end GlobalTheory.MBLow.Cl

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeValue_complexPoints_eq_frameAlternatingProduct : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g), d.Cub → ∀ (G : Geo ν d) (x y z : Fin g → ℂ) (j : thK.{0} → D.P.L.ι),
    (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ D.P.L.U (j I)) →
    valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
      (D.cub.t.s j).val = ∏ I : thK.{0}, G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I := by
  atlas_forward_decl GlobalTheory.MBLow.Cl.cube_val_frame
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.AltJet

def thI (s : Finset (Fin 3)) : thK.{0} := ULift.up s

@[simp] theorem thI_down (s : Finset (Fin 3)) : (thI s).down = s := rfl

theorem prod_thK {M : Type*} [CommMonoid M] (f : thK.{0} → M) :
    ∏ I : thK.{0}, f I = f (thI ∅) * (f (thI {0}) * (f (thI {1}) * (f (thI {2}) *
      (f (thI {0, 1}) * (f (thI {0, 2}) * (f (thI {1, 2}) * f (thI {0, 1, 2}))))))) := by
  refine (Fintype.prod_equiv (Equiv.ulift.symm : Finset (Fin 3) ≃ thK.{0}) (fun I => f (thI I)) f
    (fun _ => rfl)).symm.trans ?_
  have hu : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  rw [hu]
  simp (config := {decide := true}) [Finset.prod_insert]

theorem sum_thK {M : Type*} [AddCommMonoid M] (f : thK.{0} → M) :
    ∑ I : thK.{0}, f I = f (thI ∅) + (f (thI {0}) + (f (thI {1}) + (f (thI {2}) +
      (f (thI {0, 1}) + (f (thI {0, 2}) + (f (thI {1, 2}) + f (thI {0, 1, 2}))))))) := by
  refine (Fintype.sum_equiv (Equiv.ulift.symm : Finset (Fin 3) ≃ thK.{0}) (fun I => f (thI I)) f
    (fun _ => rfl)).symm.trans ?_
  have hu : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  rw [hu]
  simp (config := {decide := true}) [Finset.sum_insert]

theorem thε_thI_empty : thε (thI ∅) = -1 := by decide
theorem thε_thI_0 : thε (thI {0}) = 1 := by decide
theorem thε_thI_1 : thε (thI {1}) = 1 := by decide
theorem thε_thI_2 : thε (thI {2}) = 1 := by decide
theorem thε_thI_01 : thε (thI {0, 1}) = -1 := by decide
theorem thε_thI_02 : thε (thI {0, 2}) = -1 := by decide
theorem thε_thI_12 : thε (thI {1, 2}) = -1 := by decide
theorem thetaCubeSign_full : thε (thI {0, 1, 2}) = 1 := by decide

theorem hasFDerivAt_prod_zpow_of_eq_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {κ : Type*} [DecidableEq κ] (s : Finset κ) (h : κ → E → ℂ) (h' : κ → E →L[ℂ] ℂ) (n : κ → ℤ) (x : E)
    (hd : ∀ i ∈ s, HasFDerivAt (h i) (h' i) x) (hn : ∀ i ∈ s, h i x ≠ 0)
    (h1 : ∏ i ∈ s, h i x ^ n i = 1) :
    HasFDerivAt (fun z => ∏ i ∈ s, h i z ^ n i) (∑ i ∈ s, ((n i : ℂ) / h i x) • h' i) x := by
  have hz : ∀ i ∈ s, HasFDerivAt (fun z => h i z ^ n i)
      (((n i : ℂ) * h i x ^ (n i - 1)) • h' i) x := by
    intro i hi
    exact (hasDerivAt_zpow (n i) (h i x) (Or.inl (hn i hi))).comp_hasFDerivAt x (hd i hi)
  have := HasFDerivAt.finsetProd (g := fun i z => h i z ^ n i) hz
  refine this.congr_fderiv (Finset.sum_congr rfl fun i hi => ?_)
  have hm := Finset.mul_prod_erase s (fun j => h j x ^ n j) hi
  rw [h1] at hm
  have hne : h i x ^ n i ≠ 0 := zpow_ne_zero _ (hn i hi)
  have he : ∏ j ∈ s.erase i, h j x ^ n j = (h i x ^ n i)⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hm)
  rw [he, smul_smul, zpow_sub_one₀ (hn i hi)]
  congr 1
  field_simp

section
variable {E : Type*} [AddCommMonoid E] (a b c : E)
@[simp] theorem vsum_empty : ∑ i ∈ (∅ : Finset (Fin 3)), ![a, b, c] i = 0 := Finset.sum_empty
@[simp] theorem vsum_0 : ∑ i ∈ ({0} : Finset (Fin 3)), ![a, b, c] i = a := Finset.sum_singleton _ _
@[simp] theorem vsum_1 : ∑ i ∈ ({1} : Finset (Fin 3)), ![a, b, c] i = b := Finset.sum_singleton _ _
@[simp] theorem vsum_2 : ∑ i ∈ ({2} : Finset (Fin 3)), ![a, b, c] i = c := Finset.sum_singleton _ _
@[simp] theorem vsum_01 : ∑ i ∈ ({0, 1} : Finset (Fin 3)), ![a, b, c] i = a + b :=
  Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)
@[simp] theorem vsum_02 : ∑ i ∈ ({0, 2} : Finset (Fin 3)), ![a, b, c] i = a + c :=
  Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2)
@[simp] theorem vsum_12 : ∑ i ∈ ({1, 2} : Finset (Fin 3)), ![a, b, c] i = b + c :=
  Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)
@[simp] theorem sum_univ_finThree_vecThree : ∑ i ∈ ({0, 1, 2} : Finset (Fin 3)), ![a, b, c] i = a + (b + c) := by
  rw [Finset.sum_insert (by decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3))), vsum_12]
  rfl
end

theorem value_and_fderiv_at_zero : ∀ {g : ℕ} (x y W : Fin g → ℂ) (fr : thK.{0} → (Fin g → ℂ) → ℂ) (F : (Fin g → ℂ) → ℂ),
    F =ᶠ[nhds 0] (fun z => ∏ I : thK.{0}, fr I (∑ i ∈ I.down, ![x, y, z] i) ^ thε I) →
    (∀ I : thK.{0}, DifferentiableAt ℂ (fr I) (∑ i ∈ I.down, ![x, y, 0] i)) →
    (∀ I : thK.{0}, fr I (∑ i ∈ I.down, ![x, y, 0] i) ≠ 0) →
    (∀ I : thK.{0}, 2 ∉ I.down → fr (ULift.up (insert 2 I.down)) = fr I) →
    F 0 = 1 ∧ fderiv ℂ F 0 W =
      fderiv ℂ (fr (ULift.up {0, 1, 2})) (x + y) W / fr (ULift.up {0, 1, 2}) (x + y) +
        fderiv ℂ (fr (ULift.up {2})) 0 W / fr (ULift.up {2}) 0 -
        fderiv ℂ (fr (ULift.up {0, 2})) x W / fr (ULift.up {0, 2}) x -
        fderiv ℂ (fr (ULift.up {1, 2})) y W / fr (ULift.up {1, 2}) y := by
  intro g x y W fr F hF hd hn hpair
  show F 0 = 1 ∧ fderiv ℂ F 0 W =
      fderiv ℂ (fr (thI {0, 1, 2})) (x + y) W / fr (thI {0, 1, 2}) (x + y) +
        fderiv ℂ (fr (thI {2})) 0 W / fr (thI {2}) 0 -
        fderiv ℂ (fr (thI {0, 2})) x W / fr (thI {0, 2}) x -
        fderiv ℂ (fr (thI {1, 2})) y W / fr (thI {1, 2}) y
  have hw : ∀ I : thK.{0}, HasFDerivAt (fun z : Fin g → ℂ => ∑ i ∈ I.down, ![x, y, z] i)
      (∑ i ∈ I.down, ![0, 0, ContinuousLinearMap.id ℂ (Fin g → ℂ)] i) 0 := by
    intro I
    refine HasFDerivAt.fun_sum (A := fun i (z : Fin g → ℂ) => ![x, y, z] i) (fun i _ => ?_)
    fin_cases i
    · exact hasFDerivAt_const x (0 : Fin g → ℂ)
    · exact hasFDerivAt_const y (0 : Fin g → ℂ)
    · exact hasFDerivAt_id (0 : Fin g → ℂ)
  have hc : ∀ I : thK.{0}, HasFDerivAt (fun z : Fin g → ℂ => fr I (∑ i ∈ I.down, ![x, y, z] i))
      ((fderiv ℂ (fr I) (∑ i ∈ I.down, ![x, y, 0] i)).comp
        (∑ i ∈ I.down, ![0, 0, ContinuousLinearMap.id ℂ (Fin g → ℂ)] i)) 0 :=
    fun I => (hd I).hasFDerivAt.comp (0 : Fin g → ℂ) (hw I)
  have p0 : fr (thI {2}) = fr (thI ∅) := hpair (thI ∅) (by decide)
  have p1 : fr (thI {0, 2}) = fr (thI {0}) :=
    (congrArg (fun s => fr (thI s)) (by decide : ({0, 2} : Finset (Fin 3)) = insert 2 {0})).trans
      (hpair (thI {0}) (by decide))
  have p2 : fr (thI {1, 2}) = fr (thI {1}) :=
    (congrArg (fun s => fr (thI s)) (by decide : ({1, 2} : Finset (Fin 3)) = insert 2 {1})).trans
      (hpair (thI {1}) (by decide))
  have p3 : fr (thI {0, 1, 2}) = fr (thI {0, 1}) :=
    (congrArg (fun s => fr (thI s)) (by decide : ({0, 1, 2} : Finset (Fin 3)) = insert 2 {0, 1})).trans
      (hpair (thI {0, 1}) (by decide))
  have n0 := hn (thI ∅)
  have n1 := hn (thI {0})
  have n2 := hn (thI {1})
  have n3 := hn (thI {0, 1})
  simp only [thI_down, vsum_empty, vsum_0, vsum_1, vsum_01] at n0 n1 n2 n3
  have hP0 : ∏ I : thK.{0}, fr I (∑ i ∈ I.down, ![x, y, 0] i) ^ thε I = 1 := by
    rw [prod_thK]
    simp only [thI_down, vsum_empty, vsum_0, vsum_1, vsum_2, vsum_01, vsum_02, vsum_12, sum_univ_finThree_vecThree,
      thε_thI_empty, thε_thI_0, thε_thI_1, thε_thI_2, thε_thI_01, thε_thI_02, thε_thI_12,
      thetaCubeSign_full, p0, p1, p2, p3, add_zero, zpow_one, _root_.zpow_neg, zpow_one]
    field_simp
  refine ⟨by rw [hF.eq_of_nhds]; exact hP0, ?_⟩
  classical
  have hPd := hasFDerivAt_prod_zpow_of_eq_one (Finset.univ : Finset thK.{0})
    (fun (I : thK.{0}) (z : Fin g → ℂ) => fr I (∑ i ∈ I.down, ![x, y, z] i)) _ thε 0
    (fun I _ => hc I) (fun I _ => hn I) hP0
  rw [hF.fderiv_eq (𝕜 := ℂ), hPd.fderiv]
  rw [ContinuousLinearMap.sum_apply, sum_thK]
  simp only [thI_down, vsum_empty, vsum_0, vsum_1, vsum_2, vsum_01, vsum_02, vsum_12, sum_univ_finThree_vecThree,
      thε_thI_empty, thε_thI_0, thε_thI_1, thε_thI_2, thε_thI_01, thε_thI_02, thε_thI_12,
      thetaCubeSign_full, add_zero, zero_add, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply, map_zero, smul_zero,
      smul_eq_mul, Int.cast_one, Int.cast_neg]
  ring

end GlobalTheory.AltJet
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternatingCubeProduct_value_fderiv_at_zero : ∀ {g : ℕ} (x y W : Fin g → ℂ) (fr : thK.{0} → (Fin g → ℂ) → ℂ) (F : (Fin g → ℂ) → ℂ),
    F =ᶠ[nhds 0] (fun z => ∏ I : thK.{0}, fr I (∑ i ∈ I.down, ![x, y, z] i) ^ thε I) →
    (∀ I : thK.{0}, DifferentiableAt ℂ (fr I) (∑ i ∈ I.down, ![x, y, 0] i)) →
    (∀ I : thK.{0}, fr I (∑ i ∈ I.down, ![x, y, 0] i) ≠ 0) →
    (∀ I : thK.{0}, 2 ∉ I.down → fr (ULift.up (insert 2 I.down)) = fr I) →
    F 0 = 1 ∧ fderiv ℂ F 0 W =
      fderiv ℂ (fr (ULift.up {0, 1, 2})) (x + y) W / fr (ULift.up {0, 1, 2}) (x + y) +
        fderiv ℂ (fr (ULift.up {2})) 0 W / fr (ULift.up {2}) 0 -
        fderiv ℂ (fr (ULift.up {0, 2})) x W / fr (ULift.up {0, 2}) x -
        fderiv ℂ (fr (ULift.up {1, 2})) y W / fr (ULift.up {1, 2}) y := by
  atlas_forward_decl GlobalTheory.AltJet.value_and_fderiv_at_zero
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.JetGeo

open ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums

section Val
variable {A : Type} [CommRing A] {X Y Z : Scheme.{0}}

theorem valR_app (x : Sp A ⟶ Y) (q : Y ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    valR x (q ⁻¹ᵁ W) ((q.app W).hom f) = valR (x ≫ q) W f := by
  by_cases hx : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ W)
  · rw [Scheme.Hom.app_eq_appLE]
    exact GlobalTheory.ZH.FormCount.valR_appLE x q W _ le_rfl f hx
  · have hx' : ¬ ⊤ ≤ (x ≫ q) ⁻¹ᵁ W := hx
    unfold valR
    rw [dif_neg hx, dif_neg hx']

theorem valR_res' (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U) (e' : U ≤ V) (f : Γ(X, U)) :
    valR x V (resG X e f) = valR x U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ V
  · exact GlobalTheory.ZH.CrdCalc.valR_res x e h f
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ U := fun hU => h (hU.trans (x.preimage_mono e'))
    unfold valR
    rw [dif_neg h, dif_neg h']

theorem valR_pullGen (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (x : Sp A ⟶ Z) (j : K → L.ι) :
    valR x (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε c h).s j).val =
      valR (x ≫ h) (LB.wchart L φ j) (c.s j).val := by
  have e' : h ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => h ≫ φ k) j :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have e : LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  change valR x _ (resG Z e ((h.app _).hom (c.s j).val)) = _
  rw [valR_res' x e e']
  exact valR_app x h _ _

end Val

theorem ex_zero {B : NumB ℂ} {g : ℕ} (d : AB B g) : d.ex 0 = 1 := by
  have := d.ex_add 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem ex_sum {B : NumB ℂ} {g : ℕ} (d : AB B g) {J : Type} (s : Finset J) (v : J → Fin g → ℂ) :
    d.ex (∑ i ∈ s, v i) = ∏ i ∈ s, d.ex (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ex_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, d.ex_add, ih]

section Pts
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem thφ_pt (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) (I : thK.{0}) :
    (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left ≫ thφ D.P.A (x3 D.P.A) I =
      (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left := by
  show _ ≫ (psum D.P.A (x3 D.P.A) I.down).left = _
  rw [← Over.comp_left, psum_eq_prod, comp_prod]
  have h3 : ∀ i, lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z))) ≫ x3 D.P.A i =
      ν.eA (d.ex (![x, y, z] i)) := by
    intro i; fin_cases i <;> simp [x3]
  simp_rw [h3, ← map_prod, ← ex_sum]

end Pts

theorem jet_geo : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (gm : GtPt D (TE R ℂ)),
    (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    ∃ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)),
      vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
        valR (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) gm.b).left U f ∧
      ⊤ ≤ ptB ν d 0 ⁻¹ᵁ U ∧
      ∀ z, ⊤ ≤ ptB ν d z ⁻¹ᵁ U →
        (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ
          D.P.L.U (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)) ∧
        valF (ptB ν d z) U f =
          valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left
            (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left))
            (D.cub.t.s (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)).val := by
  intro R _ _ D _ N g ν d gm ⟨o, ho, hp⟩ χ χ' x y hx hy
  classical

  have hρ : redE ℂ ≫ (TE R ℂ).hom = (TF (R := R) ℂ).hom := by
    have e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext; simp
    simp only [TE, Over.mk_hom, redE, spMap]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_id, Spec.map_id,
      Category.id_comp]
  let ρ : TF (R := R) ℂ ⟶ TE R ℂ := Over.homMk (redE ℂ) hρ
  let P3 : (Fin g → ℂ) → (TF (R := R) ℂ ⟶ G3 D.P.A) := fun z =>
    lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))
  let q : DegPre.BF D ℂ ⟶ G3 D.P.A :=
    lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') (DegPre.prB D ℂ))
  let h := (lift (DegPre.cT D (TE R ℂ) χ) (lift (DegPre.cT D (TE R ℂ) χ') gm.b))
  have hb : ρ ≫ gm.b = ν.eA (d.ex 0) := by
    rw [ex_zero, map_one]
    ext1
    show redE ℂ ≫ gm.b.left = _
    rw [← hp.1, ho.1]
    rfl
  have hred : ρ ≫ h = P3 0 := by
    simp only [h, P3, comp_lift, hb, DegPre.cT, comp_toUnit_assoc]
    rw [show toUnit _ ≫ D.c χ = ν.eA (d.ex x) from hx.symm, show toUnit _ ≫ D.c χ' = ν.eA (d.ex y) from hy.symm]
  have hq : lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) gm.b ≫ q = h := by
    simp only [q, h, comp_lift, comp_toUnit_assoc, DegPre.prB, lift_snd, DegPre.cT]
  have hpt : ∀ z, ptB ν d z ≫ q.left = (P3 z).left := by
    intro z
    rw [ptB, ← Over.comp_left]
    congr 1
    simp only [q, P3, comp_lift, comp_toUnit_assoc, DegPre.prB, lift_snd]
    rw [show toUnit _ ≫ D.c χ = ν.eA (d.ex x) from hx.symm, show toUnit _ ≫ D.c χ' = ν.eA (d.ex y) from hy.symm]
  have e3 : ∀ z I, (P3 z).left ≫ thφ D.P.A (x3 D.P.A) I = (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left :=
    fun z I => thφ_pt ν d x y z I
  let j0 : thK.{0} → D.P.L.ι := fun I => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left
  let W0 := LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j0
  refine ⟨q.left ⁻¹ᵁ W0, (q.left.app W0).hom (D.cub.t.s j0).val, ?_, ?_, ?_⟩
  ·
    have hj : (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ h.left ≫ thφ D.P.A (x3 D.P.A) k)) = j0 := by
      funext I
      rw [Category.id_comp, ← Category.assoc, show redE ℂ ≫ h.left = (P3 0).left from congrArg Over.Hom.left hred,
        e3]
    refine Eq.trans ?_ (valR_app _ q.left W0 _).symm
    rw [← Over.comp_left, hq]
    unfold vE DegPre.cubAtT
    refine (valR_pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t h.left (𝟙 _) _).trans ?_
    rw [Category.id_comp]
    have key : ∀ j j' : thK.{0} → D.P.L.ι, j = j' → valR h.left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
        (D.cub.t.s j).val = valR h.left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j') (D.cub.t.s j').val := by
      rintro _ _ rfl; rfl
    exact key _ _ hj
  · intro p _
    change (ptB ν d 0 ≫ q.left).base p ∈ W0
    rw [hpt]
    refine Set.mem_iInter.2 fun I => ?_
    have := ν.good ((P3 0).left ≫ thφ D.P.A (x3 D.P.A) I) (Set.mem_univ p)
    rw [e3] at this
    change ((P3 0).left ≫ thφ D.P.A (x3 D.P.A) I).base p ∈ D.P.L.U (j0 I)
    rw [e3]
    exact this
  · intro z hz
    refine ⟨fun I p _ => ?_, ?_⟩
    · have hm : (ptB ν d z ≫ q.left).base p ∈ W0 := hz (Set.mem_univ p)
      rw [hpt] at hm
      have := LB.wchart_le D.P.L (thφ D.P.A (x3 D.P.A)) j0 I hm
      rw [← e3 z I]
      exact this
    · change valR (ptB ν d z) _ _ = valR _ _ _
      refine (valR_app (ptB ν d z) q.left W0 _).trans ?_
      rw [hpt]

end GlobalTheory.MBLow.JetGeo
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeValue_constPoints_tangent_eq_dualFibreValue : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (gm : GtPt D (TE R ℂ)),
    (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    ∃ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)),
      vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
        valR (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) gm.b).left U f ∧
      ⊤ ≤ ptB ν d 0 ⁻¹ᵁ U ∧
      ∀ z, ⊤ ≤ ptB ν d z ⁻¹ᵁ U →
        (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ
          D.P.L.U (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)) ∧
        valF (ptB ν d z) U f =
          valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left
            (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left))
            (D.cub.t.s (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)).val := by
  atlas_forward_decl GlobalTheory.MBLow.JetGeo.jet_geo
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubeJet

theorem cube_jet : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (G : Geo ν d),
    (∀ (x y z : Fin g → ℂ) (j : thK.{0} → D.P.L.ι),
      (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ D.P.L.U (j I)) →
      valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
        (D.cub.t.s j).val = ∏ I : thK.{0}, G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I) →
    ∀ (W : Fin g → ℂ) (gm : GtPt D (TE R ℂ)), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    IsD ν d W gm.b → ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
      1 + TrivSqZeroExt.inr
        (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex (x + y))).left)) (x + y) W / G.frG (ν.J (ν.eA (d.ex (x + y))).left) (x + y) +
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W / G.frG (ν.J (ν.eA (d.ex 0)).left) 0 -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex x)).left)) x W / G.frG (ν.J (ν.eA (d.ex x)).left) x -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex y)).left)) y W / G.frG (ν.J (ν.eA (d.ex y)).left) y) := by
  intro R _ _ D _ N g ν d G hprod W gm h0 hD χ χ' x y hx hy
  obtain ⟨U, f, hv, hU0, hUz⟩ := GlobalTheory.T.cubeValue_constPoints_tangent_eq_dualFibreValue ν d gm h0 χ χ' x y hx hy
  rw [hv, hD U f hU0]
  have hO : IsOpen {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} := (G.hol U f).1
  have hFeq : (fun z => valF (ptB ν d z) U f) =ᶠ[nhds 0] fun z => ∏ I : thK.{0},
      G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I := by
    filter_upwards [hO.mem_nhds hU0] with z hz
    obtain ⟨hI, hval⟩ := hUz z hz
    rw [hval]
    exact hprod x y z _ hI
  have hopen : ∀ i, IsOpen {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ D.P.L.U i} := fun i => by
    have e : ∀ z, (ν.eA (d.ex z)).left = ptB ν d z ≫ (DegPre.prB D ℂ).left := fun z => by
      rw [ptB, DegPre.prB, ← Over.comp_left, lift_snd]
    have := (G.hol ((DegPre.prB D ℂ).left ⁻¹ᵁ D.P.L.U i) 0).1
    simpa only [e, Scheme.Hom.comp_preimage] using this
  have hd : ∀ I : thK.{0}, DifferentiableAt ℂ (G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left))
      (∑ i ∈ I.down, ![x, y, 0] i) := fun I =>
    (G.fr_hol _).differentiableAt ((hopen _).mem_nhds (ν.good _))
  have hn : ∀ I : thK.{0}, G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)
      (∑ i ∈ I.down, ![x, y, 0] i) ≠ 0 := fun I => by
    rw [← G.fr_eq]
    exact mul_ne_zero (Units.ne_zero _) (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)
  have hpair : ∀ I : thK.{0}, 2 ∉ I.down →
      G.frG (ν.J (ν.eA (d.ex (∑ i ∈ (insert 2 I.down), ![x, y, 0] i))).left) =
        G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left) := fun I h2 => by
    rw [Finset.sum_insert h2]
    simp
  obtain ⟨h1, h2⟩ := GlobalTheory.T.alternatingCubeProduct_value_fderiv_at_zero x y W (fun I : thK.{0} => G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)) _
    hFeq hd hn hpair
  rw [h1, h2]
  simp [Finset.sum_insert]

end GlobalTheory.MBLow.Cl.CubeJet
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cube_value_eq_first_jet_alternating_product : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (G : Geo ν d),
    (∀ (x y z : Fin g → ℂ) (j : thK.{0} → D.P.L.ι),
      (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ D.P.L.U (j I)) →
      valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
        (D.cub.t.s j).val = ∏ I : thK.{0}, G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I) →
    ∀ (W : Fin g → ℂ) (gm : GtPt D (TE R ℂ)), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    IsD ν d W gm.b → ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
      1 + TrivSqZeroExt.inr
        (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex (x + y))).left)) (x + y) W / G.frG (ν.J (ν.eA (d.ex (x + y))).left) (x + y) +
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W / G.frG (ν.J (ν.eA (d.ex 0)).left) 0 -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex x)).left)) x W / G.frG (ν.J (ν.eA (d.ex x)).left) x -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex y)).left)) y W / G.frG (ν.J (ν.eA (d.ex y)).left) y) := by
  atlas_forward_decl GlobalTheory.MBLow.Cl.CubeJet.cube_jet
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.JetGen

theorem mul_dot_basis {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (f : X →+ ℂ) {c : ℂ}
    (hc : c ≠ 0) (χ : X) : c * (co bX χ ⬝ᵥ fun l => f (bX l) / c) = f χ := by
  conv_rhs => rw [← bX.sum_repr χ]
  rw [map_sum, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_zsmul, zsmul_eq_mul]
  simp only [co]
  field_simp

theorem dual_alg (A : DualNumber ℂ) {c d c0 d0 l : ℂ} (hc : c ≠ 0) (hc0 : c0 ≠ 0) (hA : A.fst = 1)
    (hl : l = A.snd + d / c - d0 / c0) :
    A * (TrivSqZeroExt.inl c + TrivSqZeroExt.inr d) * TrivSqZeroExt.inl c0 =
      (1 + TrivSqZeroExt.inr l) * TrivSqZeroExt.inl c * (TrivSqZeroExt.inl c0 + TrivSqZeroExt.inr d0) := by
  ext
  · simp [hA]
  · simp [hA, hl]
    field_simp
    ring

theorem co_add {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (χ χ' : X) :
    co bX (χ + χ') = co bX χ + co bX χ' := by
  ext l; simp [co]

theorem tangent_generators : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X)
    (d : CD N g r bX) (G : Geo ν d.toAB) (gm : GtPt D (TE R ℂ)) (W : Fin g → ℂ),
    (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → IsD ν d.toAB W gm.b →
    ∃ T : Fin r → ℂ, ∀ (χ : N.X) (ct : Fin g → ℂ), ct = d.t12 *ᵥ co bX χ →
      vE (gm.s (ν.eX χ)) (𝟙 _) ν.J * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) +
        TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex ct)).left)) ct W) : DualNumber ℂ) *
        TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) =
      (1 + TrivSqZeroExt.inr ((2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ T))) *
        TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) *
        (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) +
          TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) := by
  intro R _ _ _ _ D _ _ _ N ν g r bX d G gm W h0 hD

  set cf : (Fin g → ℂ) → ℂ := fun w => G.frG (ν.J (ν.eA (d.ex w)).left) w with hcf
  set df : (Fin g → ℂ) → ℂ := fun w => fderiv ℂ (G.frG (ν.J (ν.eA (d.ex w)).left)) w W with hdf
  have hc : ∀ w, cf w ≠ 0 := fun w => by
    simp only [hcf, ← G.fr_eq]
    exact mul_ne_zero (Units.ne_zero _) (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)
  set Dl : (Fin g → ℂ) → ℂ := fun w => df w / cf w with hDl
  set A : N.X → DualNumber ℂ := fun χ => vE (gm.s (ν.eX χ)) (𝟙 _) ν.J with hA
  have hA1 : ∀ χ, (A χ).fst = 1 := fun χ => GlobalTheory.T.torusExtension_characterValue_constantTerm_one ν gm h0 (ν.eX χ)
  set ct : N.X → (Fin g → ℂ) := fun χ => d.t12 *ᵥ co bX χ with hct
  have hct_add : ∀ χ χ', ct (χ + χ') = ct χ + ct χ' := fun χ χ' => by
    simp only [hct, co_add, Matrix.mulVec_add]
  have hx : ∀ χ, ν.eA (d.ex (ct χ)) = DegPre.cF D ℂ (ν.eX χ) := fun χ => by
    rw [← d.c_eq]; exact ν.c_eq χ
  have hprod := fun x y z j hj => GlobalTheory.T.cubeValue_complexPoints_eq_frameAlternatingProduct ν d.toAB d.cub G x y z j hj

  have hsnd : ∀ χ χ', (A (χ + χ')).snd + (Dl (ct χ + ct χ') + Dl 0 - Dl (ct χ) - Dl (ct χ')) =
      (A χ).snd + (A χ').snd := fun χ χ' => by
    have hm := GlobalTheory.T.torusExtension_dualCharValues_mul_cube ν gm (ν.eX χ) (ν.eX χ')
    rw [GlobalTheory.T.cube_value_eq_first_jet_alternating_product ν d.toAB G hprod W gm h0 hD _ _ (ct χ) (ct χ') (hx χ) (hx χ'), ← map_add] at hm
    have e := congrArg TrivSqZeroExt.snd hm
    simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_one,
      TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op] at e
    have e1 := hA1 (χ + χ'); have e2 := hA1 χ; have e3 := hA1 χ'
    simp only [hA] at e1 e2 e3 ⊢
    rw [e1, e2, e3] at e
    linear_combination e
  clear hprod
  set ℓ : N.X → ℂ := fun χ => (A χ).snd + Dl (ct χ) - Dl 0 with hℓ
  have hℓ_add : ∀ χ χ', ℓ (χ + χ') = ℓ χ + ℓ χ' := fun χ χ' => by
    have := hsnd χ χ'
    simp only [hℓ, hct_add]
    linear_combination this
  let ℓh : N.X →+ ℂ := AddMonoidHom.mk' ℓ hℓ_add
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨fun l => ℓ (bX l) / (2 * Real.pi * Complex.I), fun χ ct' hct' => ?_⟩
  have hT : (2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ fun l => ℓ (bX l) / (2 * Real.pi * Complex.I)) = ℓ χ :=
    mul_dot_basis bX ℓh h2pi χ
  rw [hT, hct']
  exact dual_alg (A χ) (hc _) (hc 0) (hA1 χ) rfl

end GlobalTheory.MBLow.Cl.JetGen

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_tangent_generators_holomorphicFrame : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (d : CD N g r bX) (G : Geo ν d.toAB) (gm : GtPt D (TE R ℂ)) (W : Fin g → ℂ), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → IsD ν d.toAB W gm.b → ∃ T : Fin r → ℂ, ∀ (χ : N.X) (ct : Fin g → ℂ), ct = d.t12 *ᵥ co bX χ → vE (gm.s (ν.eX χ)) (𝟙 _) ν.J * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex ct)).left)) ct W) : DualNumber ℂ) * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) = (1 + TrivSqZeroExt.inr ((2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ T))) * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) := by
  atlas_forward_decl GlobalTheory.MBLow.Cl.JetGen.tangent_generators
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.JetFam

open TrivSqZeroExt in
theorem dual_unit {a a' : ℂ} (ha : a ≠ 0) : IsUnit (inl a + inr a' : DualNumber ℂ) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using ha

open TrivSqZeroExt in
theorem dual_mul {S V : DualNumber ℂ} {a a' r r' p p' e : ℂ} {k : ℕ} (ha : a ≠ 0) (hr : r ≠ 0)
    (h1 : S * inl a * (inl r + inr r') = (inl p + inr p') * (inl r + inr r') ^ k * (inl a + inr a') * inl r)
    (h2 : V * (inl a + inr a') * inl r = (1 + inr e) * inl a * (inl r + inr r')) :
    (S * V).fst / r ^ k = p ∧ (S * V).snd / r ^ k = p' + e * p + k * (r' / r) * p := by
  have ua : IsUnit (inl a : DualNumber ℂ) := by simpa using dual_unit (a' := 0) ha
  have ur : IsUnit (inl r : DualNumber ℂ) := by simpa using dual_unit (a' := 0) hr
  have hu := ((ua.mul (dual_unit (a' := r') hr)).mul (dual_unit (a' := a') ha)).mul ur
  have key : S * V = (inl p + inr p') * (inl r + inr r') ^ k * (1 + inr e) := by
    apply hu.mul_right_cancel
    linear_combination (V * (inl a + inr a') * inl r) * h1 +
      ((inl p + inr p') * (inl r + inr r') ^ k * (inl a + inr a') * inl r) * h2
  rw [key]
  constructor
  · simp [hr]
  · rcases k with _ | k
    · simp; ring
    · simp [TrivSqZeroExt.snd_pow]
      field_simp
      ring

open TrivSqZeroExt in
theorem dual_zero {V : DualNumber ℂ} {a r e : ℂ} (ha : a ≠ 0) (hr : r ≠ 0)
    (h2 : V * (inl a + inr 0) * inl r = (1 + inr e) * inl a * (inl r + inr 0)) : V = 1 + inr e := by
  have ua : IsUnit (inl a : DualNumber ℂ) := by simpa using dual_unit (a' := 0) ha
  have ur : IsUnit (inl r : DualNumber ℂ) := by simpa using dual_unit (a' := 0) hr
  apply (ua.mul ur).mul_right_cancel
  rw [inr_zero, add_zero, add_zero] at h2
  linear_combination h2

variable {g' r g : ℕ} (σ : Fin g ≃ Fin g' ⊕ Fin r)

def join (z : Fin g' → ℂ) (t : Fin r → ℂ) : Fin g → ℂ := fun j => Sum.elim z t (σ j)

theorem leftComponent_join (z : Fin g' → ℂ) (t : Fin r → ℂ) : zP σ (join σ z t) = z := by
  funext i; simp [zP, join]

theorem secondBlock_join (z : Fin g' → ℂ) (t : Fin r → ℂ) : tP σ (join σ z t) = t := by
  funext i; simp [tP, join]

theorem join_zero : join σ 0 0 = 0 := by
  funext j; simp only [join]; rcases σ j with i | i <;> simp

theorem diff_join : Differentiable ℂ fun z : Fin g' → ℂ => join σ z 0 := by
  refine differentiable_pi.2 fun j => ?_
  simp only [join]
  rcases σ j with i | i
  · simp only [Sum.elim_inl]; fun_prop
  · simp

def zL : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ.symm (Sum.inl i))

def tL (c : ℂ) (v : Fin r → ℂ) : (Fin g → ℂ) →L[ℂ] ℂ :=
  c • ∑ l, v l • ContinuousLinearMap.proj (σ.symm (Sum.inr l))

theorem zL_apply (Y : Fin g → ℂ) : zL σ Y = zP σ Y := rfl

theorem tL_apply (c : ℂ) (v : Fin r → ℂ) (Y : Fin g → ℂ) : tL σ c v Y = c * (v ⬝ᵥ tP σ Y) := by
  simp [tL, tP, dotProduct]

theorem fderiv_eq (c : ℂ) (v : Fin r → ℂ) {F : (Fin g → ℂ) → ℂ} {φ : (Fin g' → ℂ) → ℂ} (hφ : Differentiable ℂ φ)
    (h : ∀ Y, F Y = Complex.exp (c * (v ⬝ᵥ tP σ Y)) * φ (zP σ Y)) (Z : Fin g → ℂ) :
    fderiv ℂ F 0 Z = fderiv ℂ φ 0 (zP σ Z) + c * (v ⬝ᵥ tP σ Z) * φ 0 := by
  have e : F = fun Y => Complex.exp (tL σ c v Y) * φ (zL σ Y) := by
    funext Y; rw [h, tL_apply, zL_apply]
  have h1 : HasFDerivAt (fun Y => Complex.exp (tL σ c v Y)) _ (0 : Fin g → ℂ) := (tL σ c v).hasFDerivAt.cexp
  have h2 : HasFDerivAt (fun Y => φ (zL σ Y)) _ (0 : Fin g → ℂ) :=
    (hφ (zL σ 0)).hasFDerivAt.comp (0 : Fin g → ℂ) (zL σ).hasFDerivAt
  have h3 := (h1.mul h2).fderiv
  rw [e]
  refine (congrArg (fun L => L Z) h3).trans ?_
  rw [map_zero, map_zero]
  simp [tL_apply, zL_apply, mul_comm]

end GlobalTheory.MBLow.Cl.JetFam

namespace GlobalTheory.MBLow.Cl

open JetFam

theorem jet_family_deriv : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g' r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (_ : Geo ν d.toAB) (gm : GtPt D (TE R ℂ)) (W : Fin g' → ℂ), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → IsD ν d.toAB W gm.b → ∃ (Z : Fin g → ℂ) (c₀ : ℂ), zP σ Z = W ∧ (W = 0 → ∀ χ, vE (gm.s (ν.eX χ)) (𝟙 _) ν.J = 1 + TrivSqZeroExt.inr ((2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ tP σ Z))) ∧ ∀ (k : ℕ) (s : Fam D ℂ k) (f : N.X → N.A → ℂ) (α : N.X) (F : (Fin g → ℂ) → ℂ), ν.FamV s f → Differentiable ℂ F → (∀ Y h, d.IsPt σ Y h → f α h.b * h.s α = (d.fr (zP σ Y) : ℂ) ^ k * F Y) → (jc ν s gm α).fst / ν.rg ^ k = F 0 ∧ (jc ν s gm α).snd / ν.rg ^ k = fderiv ℂ F 0 Z + k * c₀ * F 0 := by
  intro R _ _ _ _ D hE hT _ N ν g' r g bX d σ G gm W ho hW
  obtain ⟨T, hT'⟩ := GlobalTheory.T.torusExtension_tangent_generators_holomorphicFrame R D hE hT N ν g' r bX d G gm W ho hW
  have hrg : ν.rg ≠ 0 := GlobalTheory.Ex.FamVal.rg_ne ν
  have hne : ∀ z, G.frG (ν.J (ν.eA (d.ex z)).left) z ≠ 0 := fun z => by
    rw [← G.fr_eq]; exact mul_ne_zero (Units.ne_zero _) hrg
  have h0 : G.frG (ν.J (ν.eA (d.ex 0)).left) 0 = ν.rg := by
    rw [← G.fr_eq, d.fr_zero]; simp
  refine ⟨join σ W T, fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W / ν.rg, leftComponent_join σ W T, ?_, ?_⟩
  · intro hW0 χ
    have := hT' χ _ rfl
    subst hW0
    rw [map_zero, map_zero] at this
    rw [secondBlock_join]
    exact dual_zero (hne _) (hne _) this
  · intro k s f α F hs hF hf
    obtain ⟨o, hz, hp⟩ := ho
    have hb : redE ℂ ≫ gm.b.left = (DegPre.zeroF D ℂ).left := by
      rw [← hz.1]; exact hp.1.symm
    have hpt := fun Y => ((GlobalTheory.MBLow.Cl.exp_onto_torusExt N g' r g bX d σ).1 Y).exists
    have hφ : Differentiable ℂ fun z => F (join σ z 0) := hF.comp (diff_join σ)
    have hA : ∀ z, f α (d.ex z) * d.fr (d.t12 *ᵥ co bX α) * d.fr z =
        F (join σ z 0) * (d.fr z : ℂ) ^ k * d.fr (d.t12 *ᵥ co bX α + z) := fun z => by
      obtain ⟨h, hh⟩ := hpt (join σ z 0)
      have e1 := hf _ h hh
      have e2 := hh.2 α
      rw [hh.1] at e1
      rw [leftComponent_join] at e1 e2
      rw [secondBlock_join] at e2
      simp only [dotProduct_zero, mul_zero, Complex.exp_zero, one_mul] at e2
      linear_combination (d.fr (d.t12 *ᵥ co bX α + z) : ℂ) * e1 - f α (d.ex z) * e2
    have hB : ∀ Y, F Y = Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (co bX α ⬝ᵥ tP σ Y)) * F (join σ (zP σ Y) 0) :=
      fun Y => by
      obtain ⟨h, hh⟩ := hpt Y
      have e1 := hf _ h hh
      have e2 := hh.2 α
      have e3 := hA (zP σ Y)
      rw [hh.1] at e1
      apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero k (d.fr (zP σ Y)).ne_zero)
        (d.fr (d.t12 *ᵥ co bX α + zP σ Y)).ne_zero)
      linear_combination (-(d.fr (d.t12 *ᵥ co bX α + zP σ Y) : ℂ)) * e1 + f α (d.ex (zP σ Y)) * e2 +
        Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (co bX α ⬝ᵥ tP σ Y)) * e3
    have h1 := GlobalTheory.T.familyMember_tangentValue_eq_firstJet R D hE hT N ν g' d.toAB G gm.b W hb hW k s f α _ _ hs (d.c_eq α) hφ hA
    have h2 := dual_mul (hne _) (hne _) h1 (hT' α _ rfl)
    rw [h0, join_zero] at h2
    rw [fderiv_eq σ _ _ hφ hB, leftComponent_join, secondBlock_join, join_zero]
    exact h2

end GlobalTheory.MBLow.Cl

end
end
