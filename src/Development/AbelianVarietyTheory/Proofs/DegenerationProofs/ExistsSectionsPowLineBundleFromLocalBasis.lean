import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleOfNormOneGenerators
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EEContainsStableWeightZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointsAndLocalRegularity
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSupIIffAndHHEqKer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreeOrthogonalSupportAndSupISpecializes
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QuadraticMapNonnegOfTendstoCofinite
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAtTestOfCen
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitExtendOfGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.PowSec
open GlobalTheory.Points

variable {X Y : Scheme.{0}} {K : Type} [Field K]

theorem le_inf' {g : Sp K ⟶ X} {U V : X.Opens} (hU : ⊤ ≤ g ⁻¹ᵁ U) (hV : ⊤ ≤ g ⁻¹ᵁ V) :
    ⊤ ≤ g ⁻¹ᵁ (U ⊓ V) := fun _ hz => ⟨hU hz, hV hz⟩

theorem le_wchart {I : Type} [Fintype I] (L : LB X) (φ : Y ⟶ X) (j : I → L.ι) {g : Sp K ⟶ Y}
    (h : ∀ i, ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U (j i)) : ⊤ ≤ g ⁻¹ᵁ LB.wchart L (fun _ => φ) j :=
  fun _ hz => Set.mem_iInter.2 fun i => h i hz

theorem of_le_wchart {I : Type} [Fintype I] {L : LB X} {φ : Y ⟶ X} {j : I → L.ι} {g : Sp K ⟶ Y}
    (h : ⊤ ≤ g ⁻¹ᵁ LB.wchart L (fun _ => φ) j) (i : I) : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U (j i) :=
  fun _ hz => Set.mem_iInter.1 (h hz) i

noncomputable def vU (g : Sp K ⟶ X) (U : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) : Γ(X, U)ˣ →* Kˣ :=
  Units.map (valMap g U h).hom.toMonoidHom

theorem vU_val (g : Sp K ⟶ X) (U : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    valF g U u.val = (vU g U h u).val := valR_eq g U h _

theorem val_unit_ne (g : Sp K ⟶ X) {U : X.Opens} (h : ⊤ ≤ g ⁻¹ᵁ U) (u : Γ(X, U)ˣ) : valF g U u.val ≠ 0 := by
  rw [vU_val g U h]; exact Units.ne_zero _

theorem val_junk (g : Sp K ⟶ X) {U : X.Opens} (h : ¬ ⊤ ≤ g ⁻¹ᵁ U) (f : Γ(X, U)) : valF g U f = 0 := dif_neg h

theorem val_linComb_g {I : Type} [Fintype I] [Unique I] (L : LB X) (φ : Y ⟶ X) (n : ℤ) (a b : L.ι) (g : Sp K ⟶ Y)
    (ha : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U a) (hb : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U b) :
    valF g _ ((LB.LinComb L (K := I) (fun _ => φ) (fun _ => n)).g (fun _ => a) (fun _ => b)).val =
      valF (g ≫ φ) _ (L.g a b).val ^ n := by
  have h := le_inf' (le_wchart L φ (fun _ : I => a) fun _ => ha) (le_wchart L φ (fun _ : I => b) fun _ => hb)
  have key : ∀ (W : Y.Opens) (_ : ⊤ ≤ g ⁻¹ᵁ W) (e : W ≤ φ ⁻¹ᵁ (L.U a ⊓ L.U b)),
      valF g W (∏ _k : I, res e (pullU φ _ (L.g a b)) ^ n).val = valF (g ≫ φ) _ (L.g a b).val ^ n := fun W h e => by
    rw [vU_val g _ h, Fintype.prod_unique, map_zpow, Units.val_zpow_eq_zpow_val, ← vU_val]
    rw [GlobalTheory.NormGlue.val_res_pullU]
    exact congrArg (· ^ n) (valR_appLE g φ e h _)
  exact key (LB.wchart L (fun _ : I => φ) (fun _ => a) ⊓ LB.wchart L (fun _ : I => φ) (fun _ => b)) h
    (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : I => φ) (fun _ => a) default))
      (inf_le_right.trans (LB.wchart_le L (fun _ : I => φ) (fun _ => b) default)))

theorem val_div_g (M L : LB X) (a b : (LB.div M L).ι) (g : Sp K ⟶ X)
    (ha : ⊤ ≤ g ⁻¹ᵁ (LB.div M L).U a) (hb : ⊤ ≤ g ⁻¹ᵁ (LB.div M L).U b) :
    valF g _ ((LB.div M L).g a b).val = valF g _ (M.g a.1 b.1).val * (valF g _ (L.g a.2 b.2).val)⁻¹ := by
  have h := le_inf' ha hb
  have key : ∀ (W A B : X.Opens) (_ : ⊤ ≤ g ⁻¹ᵁ W) (e : W ≤ A) (e' : W ≤ B) (u : Γ(X, A)ˣ) (v : Γ(X, B)ˣ),
      valF g W (res e u * (res e' v)⁻¹).val = valF g A u.val * (valF g B v.val)⁻¹ := fun W A B h e e' u v => by
    rw [vU_val g _ h, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, ← vU_val, ← vU_val]
    exact congrArg₂ (fun x y => x * y⁻¹) (valR_res g e h _) (valR_res g e' h _)
  exact key _ _ _ h _ _ _ _

theorem val_sec {H : LB X} (s : LB.Sec H) (x : Sp K ⟶ X) {j k : H.ι} (hj : ⊤ ≤ x ⁻¹ᵁ H.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valF x (H.U j) (s.f j) = valF x (H.U j ⊓ H.U k) (H.g j k).val * valF x (H.U k) (s.f k) := by
  have h := le_inf' hj hk
  have e := congrArg (valR x (H.U j ⊓ H.U k)) (s.compat j k)
  rwa [valR_mul x _ h, valR_res x _ h, valR_res x _ h] at e

theorem val_gen {H : LB X} {s : LB.Gen H} (hs : s.IsGen) (x : Sp K ⟶ X) {j k : H.ι} (hj : ⊤ ≤ x ⁻¹ᵁ H.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valF x (H.U j) (s.s j).val = valF x (H.U j ⊓ H.U k) (H.g j k).val * valF x (H.U k) (s.s k).val :=
  val_sec ⟨fun i => (s.s i).val, fun i j => congrArg Units.val (hs i j)⟩ x hj hk

theorem val_g_self {L : LB X} (hL : L.IsLB) (x : Sp K ⟶ X) {k : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    valF x _ (L.g k k).val = 1 :=
  (valR_res x _ h _).symm.trans ((congrArg (fun u : Γ(X, L.U k)ˣ => valR x _ u.val) (hL.g_self k)).trans
    (valR_one x _ h))

theorem isUnit_of_val {U : X.Opens} (f : Γ(X, U))
    (h : ∀ (K : Type) [Field K] (g : Sp K ⟶ X), ⊤ ≤ g ⁻¹ᵁ U → valF g U f ≠ 0) : IsUnit f := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx => (X.mem_basicOpen f x hx).1 ?_
  let g : Sp (X.residueField x) ⟶ X := X.fromSpecResidueField x
  have hg : ∀ w, g w = x := fun w => Scheme.fromSpecResidueField_apply _ _
  have h1 : ⊤ ≤ g ⁻¹ᵁ U := fun w _ => show g w ∈ U by rw [hg]; exact hx
  have := (le_preimage_basicOpen_iff g h1 f).2 (h _ g h1).isUnit (x := IsLocalRing.closedPoint _) trivial
  exact Set.mem_of_eq_of_mem (hg _).symm this

def Reg (y : Y) (F : ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K) : Prop :=
  ∃ (V : Y.Opens) (f : Γ(Y, V)), y ∈ V ∧ ∀ (K : Type) [Field K] (g : Sp K ⟶ Y), ⊤ ≤ g ⁻¹ᵁ V → valF g V f = F K g

section
variable {y : Y} {F F' : ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K}

theorem Reg.val (m : Y ⟶ X) {U : X.Opens} (s : Γ(X, U)) (h : m y ∈ U) : Reg y fun _ _ g => valF (g ≫ m) U s :=
  ⟨m ⁻¹ᵁ U, (m.app U).hom s, h, fun _ _ g _ => (valR_comp g m U s).symm⟩

theorem Reg.inv (m : Y ⟶ X) {U : X.Opens} (s : Γ(X, U)) (h : m y ∈ X.basicOpen s) :
    Reg y fun _ _ g => (valF (g ≫ m) U s)⁻¹ := by
  obtain ⟨u, hu⟩ : IsUnit (resG X (X.basicOpen_le s) s) := X.toRingedSpace.isUnit_res_basicOpen s
  refine ⟨m ⁻¹ᵁ X.basicOpen s, (m.app _).hom (u⁻¹).val, h, fun _ _ g hg => (valR_comp g m _ _).symm.trans ?_⟩
  replace hg : ⊤ ≤ (g ≫ m) ⁻¹ᵁ X.basicOpen s := hg
  refine (vU_val (g ≫ m) _ hg _).trans ?_
  rw [map_inv, Units.val_inv_eq_inv_val, ← vU_val, hu]
  exact congrArg (·⁻¹) (valR_res _ _ hg _)

theorem Reg.mul (h : Reg y F) (h' : Reg y F') : Reg y fun K _ g => F K g * F' K g := by
  obtain ⟨V, f, hy, hf⟩ := h
  obtain ⟨V', f', hy', hf'⟩ := h'
  refine ⟨V ⊓ V', resG Y inf_le_left f * resG Y inf_le_right f', ⟨hy, hy'⟩, fun K _ g hg => ?_⟩
  exact (valR_mul g _ hg _ _).trans (congrArg₂ (· * ·)
    ((valR_res g _ hg _).trans (hf K g (le_preimage_mono g inf_le_left hg)))
    ((valR_res g _ hg _).trans (hf' K g (le_preimage_mono g inf_le_right hg))))

theorem Reg.add (h : Reg y F) (h' : Reg y F') : Reg y fun K _ g => F K g + F' K g := by
  obtain ⟨V, f, hy, hf⟩ := h
  obtain ⟨V', f', hy', hf'⟩ := h'
  refine ⟨V ⊓ V', resG Y inf_le_left f + resG Y inf_le_right f', ⟨hy, hy'⟩, fun K _ g hg => ?_⟩
  exact (valR_add g _ hg _ _).trans (congrArg₂ (· + ·)
    ((valR_res g _ hg _).trans (hf K g (le_preimage_mono g inf_le_left hg)))
    ((valR_res g _ hg _).trans (hf' K g (le_preimage_mono g inf_le_right hg))))

theorem Reg.pow (h : Reg y F) (n : ℕ) : Reg y fun K _ g => F K g ^ n := by
  obtain ⟨V, f, hy, hf⟩ := h
  exact ⟨V, f ^ n, hy, fun K _ g hg => (valR_pow g _ hg _ _).trans (congrArg (· ^ n) (hf K g hg))⟩

theorem Reg.sum {I : Type} (s : Finset I) {F : I → ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K}
    (h : ∀ i, Reg y (F i)) : Reg y fun K _ g => ∑ i ∈ s, F i K g := by
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, 0, trivial, fun K _ g hg => valR_zero g _ hg⟩
  | insert a s ha ih => simpa only [Finset.sum_insert ha] using (h a).add ih

end

theorem exists_glue [IsIntegral Y] (V : Y.Opens) (R : ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K → Prop)
    {F : Type} [Field F] (ξ : Sp F ⟶ Y) (hξ : ∀ w, ξ w = genericPoint Y)
    (hu : ⊤ ≤ ξ ⁻¹ᵁ V → ∀ v v', R F ξ v → R F ξ v' → v = v')
    (hl : ∀ y ∈ V, ∃ (W : Y.Opens) (f : Γ(Y, W)), y ∈ W ∧
      ∀ (K : Type) [Field K] (g : Sp K ⟶ Y), ⊤ ≤ g ⁻¹ᵁ W → ⊤ ≤ g ⁻¹ᵁ V → R K g (valF g W f)) :
    ∃ f : Γ(Y, V), ∀ (K : Type) [Field K] (g : Sp K ⟶ Y), ⊤ ≤ g ⁻¹ᵁ V → R K g (valF g V f) := by
  choose W f hy hf using fun y : V => hl y.1 y.2
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun y : V => V ⊓ W y) V (fun y => homOfLE inf_le_left)
    (fun z hz => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hz, hy _⟩) (fun y => resG Y inf_le_right (f y))
    (fun a b => eq_of_valF_generic ξ hξ (U := (V ⊓ W a) ⊓ (V ⊓ W b)) fun h => by
      have h1 := le_preimage_mono ξ inf_le_left h
      have h2 := le_preimage_mono ξ inf_le_right h
      have h3 := le_preimage_mono ξ inf_le_left h1
      exact ((valR_res ξ inf_le_left h _).trans (valR_res ξ _ h1 _)).trans ((hu h3 _ _
        (hf a F ξ (le_preimage_mono ξ inf_le_right h1) h3) (hf b F ξ (le_preimage_mono ξ inf_le_right h2) h3)).trans
        ((valR_res ξ inf_le_right h _).trans (valR_res ξ _ h2 _)).symm))
  refine ⟨s, fun K _ g hg => ?_⟩
  let y : V := ⟨g (IsLocalRing.closedPoint K), hg trivial⟩
  have h1 : ⊤ ≤ g ⁻¹ᵁ W y := (le_preimage_iff g _).2 (hy y)
  have h2 := le_inf' hg h1
  have e : valF g V s = valF g (W y) (f y) := (valR_res g inf_le_left h2 s).symm.trans
    ((congrArg (valR g _) (hs y)).trans (valR_res g _ h2 _))
  exact e ▸ hf y K g h1 hg

theorem exists_generic (Y : Scheme.{0}) [IsIntegral Y] :
    ∃ (F : Type) (_ : Field F) (ξ : Sp F ⟶ Y), ∀ w, ξ w = genericPoint Y :=
  ⟨Y.residueField (genericPoint Y), inferInstance, Y.fromSpecResidueField _,
    fun _ => Scheme.fromSpecResidueField_apply _ _⟩

end GlobalTheory.ZH.PowSec
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.PowSec
open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

def GV (c : S.J → Ω) (a : Q.L.L.ι) (K : Type) [Field K] (x : Sp K ⟶ Q.G.left) (v : K) : Prop :=
  ∀ (β : Ω →+* K) (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left)
    (jP : ρ.P.L.ι), g ≫ Q.φ = x → g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt →
    r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ →
    ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP →
    ∑ i, β (c i) * valF r _ ((ρ.s i).f (fun _ => jP)) =
      valF g _ (Q.w.s (fun _ => jP, fun _ => a)).val ^ (S.N : ℤ) * v

variable {K : Type} [Field K] {c : S.J → Ω} {a a' : Q.L.L.ι}

theorem le_w {g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀} {jP : ρ.P.L.ι}
    (h : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP) (h' : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ Q.L.L.U a) :
    ⊤ ≤ g ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) (Q.L.L.pull Q.φ)).U (fun _ => jP, fun _ => a) :=
  le_inf' (le_wchart _ _ _ fun _ => h) (le_wchart _ _ _ fun _ => h')

theorem val_w {g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀} {jP jP' : ρ.P.L.ι}
    (h : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP) (h' : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ Q.L.L.U a)
    (k : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP') (k' : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ Q.L.L.U a') :
    valF g _ (Q.w.s (fun _ => jP, fun _ => a)).val =
      valF (g ≫ pullback.fst ρ.P.A.hom Q.u₀) _ (ρ.P.L.g jP jP').val * (valF (g ≫ Q.φ) _ (Q.L.L.g a a').val)⁻¹ *
        valF g _ (Q.w.s (fun _ => jP', fun _ => a')).val := by
  refine (val_gen Q.w_gen g (le_w Q h h') (le_w Q k k')).trans (congrArg (· * _) ?_)
  refine (val_div_g _ _ _ _ g (le_w Q h h') (le_w Q k k')).trans ?_
  exact congrArg₂ (fun x y => x * y⁻¹) ((val_linComb_g (I := PUnit) _ _ 1 _ _ g h k).trans (zpow_one _))
    ((val_linComb_g (I := PUnit) _ _ 1 _ _ g h' k').trans (zpow_one _))

omit Q in
theorem thetaSystem_baseSection_value_chart {r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left} {jP jP' : ρ.P.L.ι}
    (h : ⊤ ≤ (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) ⁻¹ᵁ ρ.P.L.U jP)
    (k : ⊤ ≤ (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) ⁻¹ᵁ ρ.P.L.U jP') (i : S.J) :
    valF r _ ((ρ.s i).f (fun _ => jP)) =
      valF (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) _ (ρ.P.L.g jP jP').val ^ (S.N : ℤ) *
        valF r _ ((ρ.s i).f (fun _ => jP')) :=
  (val_sec (ρ.s i) r (j := fun _ => jP) (k := fun _ => jP') (le_wchart _ _ _ fun _ => h)
    (le_wchart _ _ _ fun _ => k)).trans (congrArg (· * _) (val_linComb_g (I := Fin 1) _ _ _ _ _ r h k))

theorem exists_data (hU : (U₀ : Set M.Z).Nonempty) {Y : Scheme.{0}} (x : Y ⟶ Q.G.left) (κ : Y ⟶ Sp Ω)
    (h : x ≫ Q.G.hom = κ ≫ M.pt) : ∃ (g : Y ⟶ pullback ρ.P.A.hom Q.u₀) (r : Y ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left),
      g ≫ Q.φ = x ∧ g ≫ pullback.snd _ _ ≫ U₀.ι = κ ≫ M.pt ∧
      r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ := by
  have hr : Set.range (κ ≫ M.pt) ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := κ w) trivial
  let y : Y ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (κ ≫ M.pt) hr
  have hy : y ≫ U₀.ι = κ ≫ M.pt := IsOpenImmersion.lift_fac _ _ _
  let g : Y ⟶ pullback ρ.P.A.hom Q.u₀ := Q.cart.1.lift x y (h.trans hy.symm)
  have hg2 : g ≫ pullback.snd _ _ = y := Q.cart.1.lift_snd x y _
  refine ⟨g, pullback.lift ((g ≫ pullback.fst _ _) ≫ ρ.P.A.hom) (g ≫ pullback.fst _ _)
    (Category.comp_id _), Q.cart.1.lift_fst x y _, ?_, pullback.lift_snd _ _ _⟩
  rw [← Category.assoc, hg2, hy]

theorem exists_data' (hU : (U₀ : Set M.Z).Nonempty) (x : Sp K ⟶ Q.G.left) (β : Ω →+* K)
    (h : x ≫ Q.G.hom = spMap β ≫ M.pt) : ∃ (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀)
      (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι),
      g ≫ Q.φ = x ∧ g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt ∧
      r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ ∧
      ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP := by
  obtain ⟨g, r, h1, h2, h3⟩ := exists_data Q hU x _ h
  obtain ⟨jP, hj⟩ := exists_le_preimage_of_iSup_eq_top (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ρ.P.isLB.cover
  exact ⟨g, r, jP, h1, h2, h3, hj⟩

variable {Q} {x : Sp K ⟶ Q.G.left} {v v' : K}

theorem GV.unique (hU : (U₀ : Set M.Z).Nonempty) {β : Ω →+* K} (h : x ≫ Q.G.hom = spMap β ≫ M.pt)
    (ha : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a) (H : GV Q c a K x v) (H' : GV Q c a K x v') : v = v' := by
  obtain ⟨g, r, jP, rfl, h2, h3, hj⟩ := exists_data' Q hU x β h
  exact mul_left_cancel₀ (zpow_ne_zero _ (val_unit_ne g (le_w Q hj ha) _))
    ((H β g r jP rfl h2 h3 hj).symm.trans (H' β g r jP rfl h2 h3 hj))

theorem GV.chart (ha : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a) (ha' : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a') (H : GV Q c a K x v) :
    GV Q c a' K x (valF x _ (Q.L.L.g a' a).val ^ (S.N : ℤ) * v) := by
  rintro β g r jP rfl h2 h3 hj
  have h0 := zpow_ne_zero (S.N : ℤ) (val_unit_ne _ (le_inf' ha' ha) (Q.L.L.g a' a))
  rw [H β g r jP rfl h2 h3 hj, val_w Q hj ha' hj ha, val_g_self ρ.P.isLB _ hj, _root_.one_mul, mul_zpow, inv_zpow]
  field_simp

theorem GV.of_one {β : Ω →+* K} {g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀}
    {r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left} {jP : ρ.P.L.ι} (ha : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a) (h1 : g ≫ Q.φ = x)
    (h2 : g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt)
    (h3 : r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _)
    (hj : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP)
    (H : ∑ i, β (c i) * valF r _ ((ρ.s i).f (fun _ => jP)) =
      valF g _ (Q.w.s (fun _ => jP, fun _ => a)).val ^ (S.N : ℤ) * v) : GV Q c a K x v := by
  intro β' g' r' jP' k1 k2 k3 kj
  have : Mono Q.φ := (MorphismProperty.monomorphisms _).of_isPullback Q.cart.1.flip
    (inferInstanceAs (Mono U₀.ι))
  have := EndoExtend.isPreimmersion_pt M
  have : Mono (snd (baseOver (Sp S.R)) ρ.P.A).left := inferInstanceAs (Mono (pullback.snd (𝟙 _) ρ.P.A.hom))
  obtain rfl : g' = g := (cancel_mono Q.φ).1 (k1.trans h1.symm)
  obtain rfl : r' = r := (cancel_mono _).1 (k3.trans h3.symm)
  obtain rfl : β' = β := congrArg (·.hom) (Spec.map_injective ((cancel_mono M.pt).1 (k2.symm.trans h2)))
  subst h1
  rw [val_w Q kj ha hj ha, val_g_self Q.L.isLB _ ha, inv_one, _root_.mul_one, mul_zpow, _root_.mul_assoc, ← H,
    Finset.mul_sum, ← h3]
  rw [← h3] at kj hj
  exact Finset.sum_congr rfl fun i _ => by rw [thetaSystem_baseSection_value_chart kj hj, mul_left_comm]

section Ratio

theorem exists_pt {X : Scheme.{0}} (y : X) : ∃ (F : Type) (_ : Field F) (g : Sp F ⟶ X), ∀ w, g w = y :=
  ⟨X.residueField y, inferInstance, X.fromSpecResidueField _, fun _ => Scheme.fromSpecResidueField_apply _ _⟩

theorem exists_ne {P : Scheme.{0}} {O : LB P} {I : Type} {τ : I → O.Sec} (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤)
    (h : Sp K ⟶ P) {k : O.ι} (hk : ⊤ ≤ h ⁻¹ᵁ O.U k) : ∃ i, valF h _ ((τ i).f k) ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_le_preimage_of_iSup_eq_top h hτ
  obtain ⟨k', hk'⟩ := TopologicalSpace.Opens.mem_iSup.1 ((le_preimage_iff h _).1 hi)
  have h1 := (le_preimage_iff h _).2 hk'
  have h2 := le_preimage_mono h (P.basicOpen_le _) h1
  refine ⟨i, ?_⟩
  rw [val_sec (τ i) h hk h2]
  exact mul_ne_zero (val_unit_ne h (le_inf' hk h2) _) ((le_preimage_basicOpen_iff h h2 _).1 h1).ne_zero

theorem exists_mem_basicOpen {P : Scheme.{0}} {O : LB P} {I : Type} {τ : I → O.Sec}
    (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) (y : P) {k : O.ι} (hk : y ∈ O.U k) : ∃ i, y ∈ P.basicOpen ((τ i).f k) := by
  obtain ⟨F, _, g, hg⟩ := exists_pt y
  have h1 : ⊤ ≤ g ⁻¹ᵁ O.U k := fun w _ => show g w ∈ O.U k from Set.mem_of_eq_of_mem (hg w) hk
  obtain ⟨i, hi⟩ := exists_ne hτ g h1
  exact ⟨i, Set.mem_of_eq_of_mem (hg (IsLocalRing.closedPoint F)).symm
    ((le_preimage_basicOpen_iff g h1 _).2 hi.isUnit trivial)⟩

variable (Q) {P : Scheme.{0}} (ν : P ⟶ Q.G.left) {O : LB P} (τ : S.J → O.Sec) (b : S.J → S.J → Ω)

def Ratio (a : Q.L.L.ι) (k : O.ι) (K : Type) [Field K] (h : Sp K ⟶ P) (v : K) : Prop :=
  v ≠ 0 ∧ ∀ i, GV Q (b i) a K (h ≫ ν) (v * valF h _ ((τ i).f k))

variable {Q ν τ b} {k k' : O.ι} {h : Sp K ⟶ P}

theorem Ratio.unique (hU : (U₀ : Set M.Z).Nonempty) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) {β : Ω →+* K}
    (e : (h ≫ ν) ≫ Q.G.hom = spMap β ≫ M.pt) (ha : ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a) (hk : ⊤ ≤ h ⁻¹ᵁ O.U k)
    (H : Ratio Q ν τ b a k K h v) (H' : Ratio Q ν τ b a k K h v') : v = v' := by
  obtain ⟨i, hi⟩ := exists_ne hτ h hk
  exact mul_right_cancel₀ hi ((H.2 i).unique hU e ha (H'.2 i))

theorem Ratio.chart (ha : ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a) (hk : ⊤ ≤ h ⁻¹ᵁ O.U k)
    (ha' : ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a') (hk' : ⊤ ≤ h ⁻¹ᵁ O.U k') (H : Ratio Q ν τ b a k K h v) :
    Ratio Q ν τ b a' k' K h
      (valF (h ≫ ν) _ (Q.L.L.g a' a).val ^ (S.N : ℤ) * (valF h _ (O.g k' k).val)⁻¹ * v) := by
  have h1 := val_unit_ne _ (le_inf' hk' hk) (O.g k' k)
  refine ⟨mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (val_unit_ne _ (le_inf' ha' ha) _)) (inv_ne_zero h1)) H.1,
    fun i => ?_⟩
  convert (H.2 i).chart ha ha' using 1
  rw [val_sec (τ i) h hk' hk]
  field_simp

theorem exists_unit (hU : (U₀ : Set M.Z).Nonempty) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤)
    (hp : ∀ (K : Type) [Field K] (β : Ω →+* K) (h : Sp K ⟶ P), (h ≫ ν) ≫ Q.G.hom = spMap β ≫ M.pt →
      ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a → ⊤ ≤ h ⁻¹ᵁ O.U k → ∃ v, Ratio Q ν τ b a k K h v)
    {Y : Scheme.{0}} [IsIntegral Y] (J : Y ⟶ P) (κ : Y ⟶ Sp Ω) (hJ : (J ≫ ν) ≫ Q.G.hom = κ ≫ M.pt)
    (V : Y.Opens) (hV : V ≤ (J ≫ ν) ⁻¹ᵁ Q.L.L.U a) (hV' : V ≤ J ⁻¹ᵁ O.U k) :
    ∃ t : Γ(Y, V)ˣ, ∀ (K : Type) [Field K] (h : Sp K ⟶ Y), ⊤ ≤ h ⁻¹ᵁ V →
      Ratio Q ν τ b a k K (h ≫ J) (valF h V t.val) := by
  have hβ : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y), spMap (Spec.preimage (h ≫ κ)).hom = h ≫ κ := fun h =>
    Spec.map_preimage _
  have he : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y),
      ((h ≫ J) ≫ ν) ≫ Q.G.hom = spMap (Spec.preimage (h ≫ κ)).hom ≫ M.pt := fun h => by
    rw [hβ, Category.assoc h κ, ← hJ]; simp only [Category.assoc]
  have ha : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y), ⊤ ≤ h ⁻¹ᵁ V → ⊤ ≤ ((h ≫ J) ≫ ν) ⁻¹ᵁ Q.L.L.U a :=
    fun h hh => le_preimage_mono h hV hh
  have hk : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y), ⊤ ≤ h ⁻¹ᵁ V → ⊤ ≤ (h ≫ J) ⁻¹ᵁ O.U k :=
    fun h hh => le_preimage_mono h hV' hh
  obtain ⟨F, _, ξ, hξ⟩ := exists_generic Y
  obtain ⟨g, r, g1, g2, g3⟩ := exists_data Q hU _ κ hJ
  obtain ⟨f, hf⟩ := exists_glue V (fun K _ h v => Ratio Q ν τ b a k K (h ≫ J) v) ξ hξ
    (fun hh v v' H H' => H.unique hU hτ (he ξ) (ha ξ hh) (hk ξ hh) H') (fun y hy => by
      obtain ⟨jP, hj⟩ := exists_chart ρ.P.isLB ((g ≫ pullback.fst ρ.P.A.hom Q.u₀) y)
      obtain ⟨i, hi⟩ := exists_mem_basicOpen hτ (J y) (hV' hy)
      have m1 : r y ∈ (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).U (fun _ => jP) :=
        Set.mem_iInter.2 fun _ => by rw [← g3] at hj; exact hj
      have m2 : g y ∈ (pullback ρ.P.A.hom Q.u₀).basicOpen (Q.w.s (fun _ => jP, fun _ => a)).val := by
        rw [Scheme.basicOpen_of_isUnit _ (Units.isUnit _)]
        have := hV hy
        rw [← g1] at this
        exact ⟨Set.mem_iInter.2 fun _ => hj, Set.mem_iInter.2 fun _ => this⟩
      obtain ⟨W, f, hW, hf⟩ := ((Reg.sum Finset.univ fun l => (Reg.val κ (U := ⊤)
        ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (b i l)) trivial).mul (Reg.val r ((ρ.s l).f _) m1)).mul
        ((Reg.inv g _ m2).pow S.N)).mul (Reg.inv J _ hi)
      refine ⟨W ⊓ ((g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP ⊓ J ⁻¹ᵁ P.basicOpen ((τ i).f k)),
        resG Y inf_le_left f, ⟨hW, hj, hi⟩, fun K _ h h1 h2 => ?_⟩
      obtain ⟨v, hv⟩ := hp K _ _ (he h) (ha h h2) (hk h h2)
      have n1 : ⊤ ≤ ((h ≫ g) ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP :=
        le_preimage_mono h (inf_le_right.trans inf_le_left) h1
      have n2 : ⊤ ≤ (h ≫ J) ⁻¹ᵁ P.basicOpen ((τ i).f k) := le_preimage_mono h (inf_le_right.trans inf_le_right) h1
      have n3 : (h ≫ g) ≫ Q.φ = (h ≫ J) ≫ ν := by rw [Category.assoc, g1, Category.assoc]
      have e := hv.2 i _ (h ≫ g) (h ≫ r) jP n3 (by rw [Category.assoc, g2, hβ, Category.assoc])
        (by rw [Category.assoc, g3, Category.assoc]) n1
      have z1 : valF (h ≫ J) _ ((τ i).f k) ≠ 0 := ((le_preimage_basicOpen_iff _ (hk h h2) _).1 n2).ne_zero
      have z2 := val_unit_ne (h ≫ g) (le_w Q n1 (n3 ▸ ha h h2)) (Q.w.s (fun _ => jP, fun _ => a))
      convert hv using 1
      refine (valR_res h _ h1 _).trans ((hf K h (le_preimage_mono h inf_le_left h1)).trans ?_)
      rw [zpow_natCast] at e
      have key : ∀ (A w t : K), w ≠ 0 → t ≠ 0 → A = w ^ S.N * (v * t) → A * (w⁻¹) ^ S.N * t⁻¹ = v := by
        rintro _ w t h1 h2 rfl
        rw [inv_pow]
        field_simp
      refine key _ _ _ z2 z1 (Eq.trans (Finset.sum_congr rfl fun l _ => ?_) e)
      rw [preimage_apply (h ≫ κ) (b i l)]
      rfl)
  exact ⟨(isUnit_of_val f fun K _ h hh => (hf K h hh).1).unit, hf⟩

end Ratio

end GlobalTheory.ZH.PowSec
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem ThetaSys.proj_column_mem_of_stable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    (A : Subalgebra o Ω) (E : Submodule A (S.J → Ω)) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N)
    (h1 : ∀ i, Pi.single i (1 : Ω) ∈ E)
    (h2 : ∀ h ∈ T, ∀ v ∈ E, ((S.ρ h).map (algebraMap o Ω)).mulVec v ∈ E) (i : S.J) :
    (fun j => algebraMap o Ω (S.proj T c j i)) ∈ E := by
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  haveI : Fintype T := Fintype.ofFinite _
  have e : (fun j => algebraMap o Ω (S.proj T c j i)) =
      ∑ t : T, (algebraMap o A (Ring.inverse (Nat.card T : o) * S.ζN ^ (-(c t)).val)) •
        ((S.ρ t).map (algebraMap o Ω)).mulVec (Pi.single i 1) := by
    funext j
    simp only [ThetaSys.proj, finsum_eq_sum_of_fintype, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      Finset.mul_sum, map_sum, Finset.sum_apply, Pi.smul_apply, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.map_apply, algebraMap_smul, map_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Algebra.smul_def, map_mul, _root_.mul_assoc]
    rfl
  rw [e]
  exact E.sum_mem fun t _ => E.smul_mem _ (h2 t t.2 _ (h1 i))

theorem basis_origin_values_regular_and_unit :
    GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → S.IsEE M U₀ EE → ∀ (z : M.Z) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), x₀ ∈ S.supI M z → EE.E z = Submodule.span (M.O z) (Set.range b) → (∀ i, (b i ⬝ᵥ S.ev 0) / S.th x₀ ∈ M.O z) ∧ ∃ i, (b i ⬝ᵥ S.ev 0) / S.th x₀ ≠ 0 ∧ ((b i ⬝ᵥ S.ev 0) / S.th x₀)⁻¹ ∈ M.O z := by
  intro h₁ h₂ h₃ h₄ h₅ o Ω _ _ _ _ S ρ M U₀ EE hO hEE z x₀ b hx₀ hb
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft Ω
  haveI : CharZero Ω := ArithBase.char o
  have hL := classical_points_and_local_regularity o Ω M U₀ hO.normal
  have hT := exists_at_test_of_cen o Ω S M U₀ (GlobalTheory.T.thetaSystem_hasTests_of_real_point h₁ h₂ h₃ h₄ h₅ o Ω S ρ).1 hO
  have hS := ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S M U₀ hO
  have hI := isoFree_TT_and_supI_specializes o Ω S M U₀ hO hL hT hS
  obtain ⟨hreg, i, hne, hinv⟩ :=
    coord_regular_and_unit o Ω S M U₀ EE hO hL hT hS hI hEE z x₀ hx₀ 0 (zero_mem _)
  obtain ⟨e1, e2, -⟩ := EE_contains_stable_weightZero o Ω S M U₀ EE hO hL hT hS hI hEE z
  have hA : ∀ i, (b i ⬝ᵥ S.ev 0) / S.th x₀ ∈ M.O z := fun i =>
    hreg _ (hb ▸ Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨hA, ?_⟩
  have hv := S.proj_column_mem_of_stable (M.O z) (EE.E z) (S.TT M z) 0 e1
    (fun h hh => e2 h ((hI.1 z).2 ▸ (hI.1 z).1.1 hh)) i
  have hu : IsUnit (⟨_, hreg _ hv⟩ : M.O z) :=
    (RatModel.isUnit_O_iff _).2 ⟨div_ne_zero hne hx₀.1, by simpa only [inv_div] using hinv⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hb ▸ hv)
  have e : (⟨_, hreg _ hv⟩ : M.O z) = ∑ k, a k * ⟨_, hA k⟩ := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    simp only [← ha, sum_dotProduct, Finset.sum_div, MulMemClass.coe_mul, Subalgebra.smul_def, smul_dotProduct,
      smul_eq_mul, mul_div_assoc]
  obtain ⟨k, -, hk⟩ := IsLocalRing.exists_of_isUnit_sum (e ▸ hu)
  exact ⟨k, (RatModel.isUnit_O_iff _).1 (isUnit_of_mul_isUnit_right hk)⟩

end GlobalTheory.ZH
end

section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OriginFrame

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {Z : Scheme.{0}}

theorem sval_valueAt {a : ℤ} {s : LB.Sec (LPow A L a T)} {x : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s x τ v) (t : Z ⟶ T.left) {z : Z} {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (t ≫ (ptSecT A x).left) z J =
      gs t z ⊤ v * (val τ t z J).val := by
  have hy := hJ.mem (fun _ : Fin 1 => x.left) t
  rw [sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (t ≫ (ptSecT A x).left) z J
    (fun _ => J (t ≫ x.left)) (fun _ => by rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd])]
  refine Eq.trans ?_ ((congrArg (gs t z _) (H _)).trans ((gs_mul _ z _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_res _ z _ hy _) (gs_unit _ z _ hy _))))
  exact ((gs_res _ z _ hy _).trans (gs_pull t (ptSecT A x).left z
    (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (t ≫ x.left))) (val_le A L x _ hy) _)).symm

theorem val_rigT (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) (t : Z ⟶ T.left) {z : Z} {J} (hJ : Good L z J) :
    val (rigT A L rig T k) t z J = val rig (t ≫ T.hom) z J ^ k := by
  have hy := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) t
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ z _ hy _).trans ?_))
  exact gm_pull t T.hom z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (t ≫ T.hom ≫ eSec A)))
    (rigT_le A L _ hy) _

theorem torsFrame_pow_origin (P : PolAV S) {T : Over S} {m : ℕ}
    {rig : LB.Gen (P.L.pull (eSec P.A))} {x : T ⟶ P.A} (hx : x = 1) {τ} (H : IsTorsFrame P rig m x τ)
    (t : Z ⟶ T.left) {z : Z} {J} (hJ : Good P.L z J) :
    val τ t z J ^ (m ^ 2) = val rig (t ≫ T.hom) z J ^ (m ^ 2) := by
  subst hx
  obtain ⟨-, -, β, hβ, hn, hc⟩ := H
  have q₁ := val_corr hJ hn (t ≫ T.hom)
  have q₂ := val_corr hJ hc t
  rw [val_pull hJ, val_mul hJ, val_inv] at q₁
  rw [val_mul hJ, val_pull hJ, val_rigT _ _ _ hJ] at q₂
  have p₁ : val (rigPow P.A P.L rig ((m : ℤ) ^ 2)) (t ≫ T.hom) z J = val rig (t ≫ T.hom) z J ^ ((m : ℤ) ^ 2) :=
    map_zpow _ _ _
  have p₂ : val (powFrame P.A P.L 1 τ ((m : ℤ) ^ 2)) t z J = val τ t z J ^ ((m : ℤ) ^ 2) := map_zpow _ _ _
  have q₃ : val β (t ≫ (1 : T ⟶ P.A).left) z J = _ := q₁.trans (congrArg (· * _) p₁)
  rw [p₂, q₃, zpow_one] at q₂
  rw [← zpow_natCast, ← zpow_natCast, Nat.cast_pow, q₂]
  exact inv_mul_cancel_right _ _

theorem valF_spMap_fn {R K : Type} [CommRing R] [Field K] (y : R →+* K) (a : R) :
    valF (X := (baseOver (Sp R)).left) (spMap y) ⊤ (fn a) = y a := by
  rw [valF, dif_pos (by simp)]
  have h := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))
  have h' := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.inv_hom_id_apply] at h'
  refine Eq.trans ?_ h'.symm
  congr 1

end GlobalTheory.OriginFrame

namespace GlobalTheory

open OriginFrame ThetaScalar in

theorem basis_value_at_origin : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (y₀ : S.R →+* K) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι), r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = spMap y₀ ≫ eSec ρ.P.A → Set.range (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) ⊆ ρ.P.L.U jP → ∃ ξ : K, ξ ^ ((S.r * S.N) ^ 2) = 1 ∧ ∀ l, valF r _ ((ρ.s l).f (fun _ => jP)) = y₀ ⟨S.ev 0 l, S.ev_mem 0 l⟩ * (ξ * valF (spMap y₀) _ (ρ.rig.s (fun _ => jP)).val) ^ S.N := by
  intro o Ω _ _ _ S ρ K _ y₀ r jP hr hU
  have := ρ.P.isAb.comm
  have h0 : ρ.pt 0 = 1 := mul_left_cancel (a := ρ.pt 0) (by rw [← ρ.pt_add, add_zero, _root_.mul_one])
  let z : Sp K := IsLocalRing.closedPoint K
  let t : Sp K ⟶ (baseOver (Sp S.R)).left := spMap y₀
  have ht : t ≫ (baseOver (Sp S.R)).hom = spMap y₀ := Category.comp_id _
  have hz : (spMap y₀ ≫ eSec ρ.P.A) z ∈ ρ.P.L.U jP := hU ⟨z, by rw [hr]⟩
  obtain ⟨J, hJ, eJ⟩ := exists_good ρ.P.L ρ.P.isLB z (fun _ : PUnit => spMap y₀ ≫ eSec ρ.P.A) (fun _ => jP)
    (fun _ _ _ => rfl) (fun _ => hz)
  have hs : (t ≫ (ptSecT ρ.P.A (ρ.pt 0)).left) ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = spMap y₀ ≫ eSec ρ.P.A := by
    rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd, h0, ← ht, Category.assoc]; rfl
  have er : r = t ≫ (ptSecT ρ.P.A (ρ.pt 0)).left := by
    haveI : Mono (snd (baseOver (Sp S.R)) ρ.P.A).left :=
      inferInstanceAs (Mono (pullback.snd (𝟙 (Sp S.R)) ρ.P.A.hom))
    rw [← cancel_mono (snd (baseOver (Sp S.R)) ρ.P.A).left, hr, hs]
  have hp := torsFrame_pow_origin ρ.P h0 (ρ.fr_tors 0) t hJ
  rw [ht] at hp
  have m₁ : r z ∈ LB.wchart ρ.P.L (fun _ : Fin 1 => (snd (baseOver (Sp S.R)) ρ.P.A).left) (fun _ => jP) :=
    Set.mem_iInter.2 fun _ => hU ⟨z, rfl⟩
  have m₂ : (spMap y₀) z ∈ LB.wchart ρ.P.L (fun _ : PUnit => eSec ρ.P.A) (fun _ => jP) :=
    Set.mem_iInter.2 fun _ => hz
  have m₃ := hJ.mem (fun _ : Fin 1 => (ρ.pt 0).left) t
  have a₂ : toStk z (valF (spMap y₀) _ (ρ.rig.s (fun _ => jP)).val) = (val ρ.rig (spMap y₀) z J).val :=
    (toStk_valF_gs (spMap y₀) _ z m₂ _).trans ((gs_unit _ z _ m₂ _).trans
      (congrArg Units.val (val_of ρ.rig (spMap y₀) z J (fun _ => jP) (fun _ => eJ PUnit.unit)).symm))
  obtain ⟨a, ha⟩ : ∃ a : K, toStk z a = (val (ρ.fr 0) t z J).val :=
    ⟨_, (toStk_valF_gs t _ z m₃ _).trans (gs_unit _ z _ m₃ _)⟩
  generalize valF (spMap y₀) _ (ρ.rig.s (fun _ => jP)).val = b at a₂ ⊢
  have hb : b ≠ 0 := fun e => (val ρ.rig (spMap y₀) z J).ne_zero (by rw [← a₂, e, map_zero])
  have hab : a ^ ((S.r * S.N) ^ 2) = b ^ ((S.r * S.N) ^ 2) := (toStk z).injective (by
    rw [map_pow, map_pow, ha, a₂, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
    exact congrArg Units.val hp)
  refine ⟨a / b, by rw [div_pow, hab, div_self (pow_ne_zero _ hb)], fun l => (toStk z).injective ?_⟩
  have hv := sval_valueAt (ρ.ev_val l 0) t hJ
  have p : val (powFrame ρ.P.A ρ.P.L (ρ.pt 0) (ρ.fr 0) S.N) t z J = val (ρ.fr 0) t z J ^ (S.N : ℤ) :=
    map_zpow _ _ _
  rw [← er, p, zpow_natCast] at hv
  replace hv := (sval_of (φ := fun _ : Fin 1 => (snd (baseOver (Sp S.R)) ρ.P.A).left) (ε := fun _ => (S.N : ℤ))
    (ρ.s l) r z J (fun _ => jP) (fun _ => by rw [hr]; exact eJ PUnit.unit)).symm.trans hv
  have a₁ := toStk_valF_gs r _ z m₁ ((ρ.s l).f (fun _ => jP))
  have a₃ := toStk_valF_gs t ⊤ z trivial (fn (⟨S.ev 0 l, S.ev_mem 0 l⟩ : S.R))
  rw [valF_spMap_fn] at a₃
  refine a₁.trans (hv.trans ?_)
  rw [div_mul_cancel₀ _ hb, map_mul, map_pow, a₃, ha, Units.val_pow_eq_pow_val]

end GlobalTheory
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.FibreLinInd

theorem exists_det_ne_zero {K A : Type} [Field K] {r : ℕ} (v : A → Fin r → K)
    (h : ∀ c : Fin r → K, (∀ a, ∑ i, c i * v a i = 0) → c = 0) :
    ∃ a : Fin r → A, (Matrix.of fun k i => v (a k) i).det ≠ 0 := by
  classical
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hφ0
    have hφ' : ∀ w : Fin r → K, φ w = ∑ i, φ (Pi.single i 1) * w i := fun w => by
      rw [LinearMap.pi_apply_eq_sum_univ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul, mul_comm]
      congr 2
      ext j
      simp [Pi.single_apply, eq_comm]
    have := h (fun i => φ (Pi.single i 1)) fun a => by
      rw [← hφ']
      exact hφ (Submodule.subset_span ⟨a, rfl⟩)
    refine LinearMap.ext fun w => ?_
    rw [hφ']
    simp [congrFun this]
  obtain ⟨κ, a, -, hs, hli⟩ := exists_linearIndependent' K v
  let b : Module.Basis κ K (Fin r → K) := Module.Basis.mk hli (by rw [hs, hspan])
  let e : κ ≃ Fin r := b.indexEquiv (Pi.basisFun K (Fin r))
  refine ⟨a ∘ e.symm, ?_⟩
  have h2 : LinearIndependent K ((v ∘ a) ∘ e.symm) := hli.comp _ e.symm.injective
  have h3 : IsUnit (Matrix.of fun k i => v ((a ∘ e.symm) k) i) :=
    Matrix.linearIndependent_rows_iff_isUnit.1 h2
  exact ((Matrix.isUnit_iff_isUnit_det _).1 h3).ne_zero

theorem exists_fibrePower {G Z : Scheme.{0}} (f : G ⟶ Z) [UniversallyOpen f]
    [LocallyOfFiniteType f] (r : ℕ) :
    ∃ (P : Scheme.{0}) (p : P ⟶ Z) (π : Fin r → (P ⟶ G)), UniversallyOpen p ∧
      LocallyOfFiniteType p ∧ (∀ k, π k ≫ f = p) ∧
      ∀ (T : Scheme.{0}) (x : T ⟶ Z) (g : Fin r → (T ⟶ G)), (∀ k, g k ≫ f = x) →
        ∃ h : T ⟶ P, h ≫ p = x ∧ ∀ k, h ≫ π k = g k := by
  induction r with
  | zero =>
    exact ⟨Z, 𝟙 Z, Fin.elim0, inferInstance, inferInstance, fun k => k.elim0,
      fun T x g _ => ⟨x, by simp, fun k => k.elim0⟩⟩
  | succ r ih =>
    obtain ⟨P, p, π, h1, h2, h3, h4⟩ := ih
    refine ⟨pullback f p, pullback.snd f p ≫ p,
      Fin.cons (pullback.fst f p) (fun k => pullback.snd f p ≫ π k), inferInstance, inferInstance,
      ?_, ?_⟩
    · refine Fin.cases ?_ fun k => ?_
      · simpa using pullback.condition
      · simp [h3]
    · intro T x g hg
      obtain ⟨h, hp, hπ⟩ := h4 T x (fun k => g k.succ) fun k => hg _
      refine ⟨pullback.lift (g 0) h (by rw [hg, hp]), by rw [pullback.lift_snd_assoc, hp], ?_⟩
      refine Fin.cases ?_ fun k => ?_
      · simp [pullback.lift_fst]
      · simp [pullback.lift_snd_assoc, hπ]

theorem exists_lift {W Z : Scheme.{0}} (q : W ⟶ Z) [LocallyOfFiniteType q] {K : Type} [Field K]
    [IsAlgClosed K] (x : Sp K ⟶ Z) (w : W) (t : Sp K) (hw : q w = x t) :
    ∃ h : Sp K ⟶ W, h ≫ q = x := by
  obtain ⟨y, -, -⟩ := Scheme.Pullback.exists_preimage_pullback w t hw
  have : JacobsonSpace ↥(pullback q x) := LocallyOfFiniteType.jacobsonSpace (pullback.snd q x)
  obtain ⟨y', -, hy'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback q x)))
    ⟨y, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {y'} := hy'
  refine ⟨pointOfClosedPoint (pullback.snd q x) y' hc ≫ pullback.fst q x, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

variable {K : Type} [Field K] {P G : Scheme.{0}}

theorem top_le_iff (x : Sp K ⟶ P) (U : P.Opens) (z : Sp K) : ⊤ ≤ x ⁻¹ᵁ U ↔ x z ∈ U := by
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact ⟨fun h => h (show z ∈ (⊤ : (Sp K).Opens) from trivial),
    fun h y _ => by rw [Subsingleton.elim y z]; exact h⟩

def evalHom (h : Sp K ⟶ P) (U : P.Opens) (hU : ⊤ ≤ h ⁻¹ᵁ U) : Γ(P, U) →+* K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp (h.appLE U ⊤ hU).hom

theorem mem_basicOpen_iff (h : Sp K ⟶ P) (U : P.Opens) (hU : ⊤ ≤ h ⁻¹ᵁ U) (D : Γ(P, U))
    (t : Sp K) : h t ∈ P.basicOpen D ↔ evalHom h U hU D ≠ 0 := by
  have e : (Sp K).basicOpen (h.appLE U ⊤ hU D) = h ⁻¹ᵁ P.basicOpen D := by
    rw [Scheme.basicOpen_appLE, top_inf_eq]
  have hinj : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.bijective
  change t ∈ h ⁻¹ᵁ P.basicOpen D ↔ _
  rw [← e]
  constructor
  · intro ht h0
    have : h.appLE U ⊤ hU D = 0 := hinj.1 (by rw [map_zero]; exact h0)
    rw [this, Scheme.basicOpen_zero] at ht
    exact ht
  · intro h0
    have : IsUnit (h.appLE U ⊤ hU D) :=
      (MulEquiv.isUnit_map
        (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv).1 (IsUnit.mk0 _ h0)
    rw [Scheme.basicOpen_of_isUnit _ this]
    trivial

theorem evalHom_appLE (h : Sp K ⟶ P) (U : P.Opens) (hU : ⊤ ≤ h ⁻¹ᵁ U) (π : P ⟶ G) (V : G.Opens)
    (hV : U ≤ π ⁻¹ᵁ V) (a : Γ(G, V)) :
    evalHom h U hU (π.appLE V U hV a) = valF (h ≫ π) V a := by
  have hle : ⊤ ≤ (h ≫ π) ⁻¹ᵁ V := fun y hy => hV (hU hy)
  rw [valF, dif_pos hle, ← Scheme.Hom.appLE_comp_appLE h π V U ⊤ hV hU]
  rfl

theorem isOpen_setOf_linearIndependent_on_fibres :
    ∀ (G Z : Scheme.{0}) (f : G ⟶ Z) [Flat f] [LocallyOfFinitePresentation f] (L : LB G),
      L.IsLB → ∀ (r : ℕ) (s : Fin r → LB.Sec L), IsOpen {z : Z | ∀ (K : Type) [Field K]
        [IsAlgClosed K] (x : Sp K ⟶ Z), Set.range x = {z} → ∀ c : Fin r → K,
          (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x →
            ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0} := by
  classical
  intro G Z f _ _ L _ r s
  obtain ⟨P, p, π, h1, h2, h3, h4⟩ := exists_fibrePower f r
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  let K := AlgebraicClosure (Z.residueField z)
  let x : Sp K ⟶ Z :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) K)) ≫ Z.fromSpecResidueField z
  have hxt : ∀ t, x t = z := fun t => by
    rw [← Set.mem_singleton_iff, ← Scheme.range_fromSpecResidueField, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let t₀ : Sp K := IsLocalRing.closedPoint K
  have hx : Set.range x = {z} := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact hxt t
    · rintro rfl
      exact ⟨t₀, hxt t₀⟩
  obtain ⟨a, ha⟩ := exists_det_ne_zero
    (fun (a : {g : Sp K ⟶ G // g ≫ f = x} × L.ι) i => valF a.1.1 (L.U a.2) ((s i).f a.2))
    fun c hc => hz K x hx c fun g j hg => hc (⟨g, hg⟩, j)
  let j : Fin r → L.ι := fun k => (a k).2
  let U : P.Opens := LB.wchart L π j
  have hU : ∀ k, U ≤ π k ⁻¹ᵁ L.U (j k) := LB.wchart_le L π j
  let M : Matrix (Fin r) (Fin r) Γ(P, U) :=
    Matrix.of fun k i => (π k).appLE (L.U (j k)) U (hU k) ((s i).f (j k))
  have hM : ∀ {K : Type} [Field K] (h : Sp K ⟶ P) (hh : ⊤ ≤ h ⁻¹ᵁ U), evalHom h U hh M.det =
      (Matrix.of fun k i => valF (h ≫ π k) (L.U (j k)) ((s i).f (j k))).det := by
    intro K _ h hh
    rw [RingHom.map_det]
    congr 1
    ext k i
    exact evalHom_appLE h U hh (π k) _ (hU k) _
  let O : P.Opens := P.basicOpen M.det
  refine ⟨p '' (O : Set P), ?_, p.isOpenMap _ O.isOpen, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩ K' _ _ x' hx' c hc
    let t : Sp K' := IsLocalRing.closedPoint K'
    have ht : x' t = p w := by
      rw [← Set.mem_singleton_iff, ← hx']
      exact ⟨t, rfl⟩
    obtain ⟨h, hh⟩ := exists_lift (O.ι ≫ p) x' ⟨w, hw⟩ t ht.symm
    have hO : (h ≫ O.ι) t ∈ O := (h t).2
    have hle : ⊤ ≤ (h ≫ O.ι) ⁻¹ᵁ U := (top_le_iff _ U t).2 (P.basicOpen_le _ hO)
    have hd := (mem_basicOpen_iff _ U hle M.det t).1 hO
    rw [hM] at hd
    refine Matrix.eq_zero_of_mulVec_eq_zero hd (funext fun k => ?_)
    have := hc ((h ≫ O.ι) ≫ π k) (j k) (by rw [Category.assoc, h3, Category.assoc, hh])
    simpa [Matrix.mulVec, dotProduct, mul_comm] using this
  · obtain ⟨h, hp, hπ⟩ := h4 (Sp K) x (fun k => (a k).1.1) fun k => (a k).1.2
    have hle : ⊤ ≤ h ⁻¹ᵁ U := by
      intro t ht
      refine Set.mem_iInter.2 fun k => ?_
      have hk : ⊤ ≤ (a k).1.1 ⁻¹ᵁ L.U (j k) := by
        by_contra hn
        exact ha (Matrix.det_eq_zero_of_row_eq_zero k fun i => dif_neg hn)
      have := hk ht
      rw [← hπ k] at this
      exact this
    refine ⟨h t₀, (mem_basicOpen_iff h U hle M.det t₀).2 ?_, ?_⟩
    · rw [hM]
      simp only [hπ]
      exact ha
    · rw [← Scheme.Hom.comp_apply, hp, hxt]

end GlobalTheory.FibreLinInd
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.FibreLinInd

theorem geometric_of_field (G Z : Scheme.{0}) (f : G ⟶ Z) [Flat f]
    [LocallyOfFinitePresentation f] (L : LB G) (r : ℕ) (s : Fin r → LB.Sec L) (z : Z)
    (K : Type) [Field K] (x : Sp K ⟶ Z) (hx : Set.range x = {z})
    (hz : ∀ c : Fin r → K, (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x →
            ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0)
    (K' : Type) [Field K'] [IsAlgClosed K'] (x' : Sp K' ⟶ Z) (hx' : Set.range x' = {z})
    (c : Fin r → K') (hc : ∀ (g : Sp K' ⟶ G) (j : L.ι), g ≫ f = x' →
            ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) : c = 0 := by
  classical
  obtain ⟨P, p, π, h1, h2, h3, h4⟩ := exists_fibrePower f r
  have hxt : ∀ t, x t = z := fun t => by
    rw [← Set.mem_singleton_iff, ← hx]
    exact ⟨t, rfl⟩
  let t₀ : Sp K := IsLocalRing.closedPoint K
  obtain ⟨a, ha⟩ := exists_det_ne_zero
    (fun (a : {g : Sp K ⟶ G // g ≫ f = x} × L.ι) i => valF a.1.1 (L.U a.2) ((s i).f a.2))
    fun c hc => hz c fun g j hg => hc (⟨g, hg⟩, j)
  let j : Fin r → L.ι := fun k => (a k).2
  let U : P.Opens := LB.wchart L π j
  have hU : ∀ k, U ≤ π k ⁻¹ᵁ L.U (j k) := LB.wchart_le L π j
  let M : Matrix (Fin r) (Fin r) Γ(P, U) :=
    Matrix.of fun k i => (π k).appLE (L.U (j k)) U (hU k) ((s i).f (j k))
  have hM : ∀ {K : Type} [Field K] (h : Sp K ⟶ P) (hh : ⊤ ≤ h ⁻¹ᵁ U), evalHom h U hh M.det =
      (Matrix.of fun k i => valF (h ≫ π k) (L.U (j k)) ((s i).f (j k))).det := by
    intro K _ h hh
    rw [RingHom.map_det]
    congr 1
    ext k i
    exact evalHom_appLE h U hh (π k) _ (hU k) _
  let O : P.Opens := P.basicOpen M.det
  have hmem : z ∈ p '' (O : Set P) := by
    obtain ⟨h, hp, hπ⟩ := h4 (Sp K) x (fun k => (a k).1.1) fun k => (a k).1.2
    have hle : ⊤ ≤ h ⁻¹ᵁ U := by
      intro t ht
      refine Set.mem_iInter.2 fun k => ?_
      have hk : ⊤ ≤ (a k).1.1 ⁻¹ᵁ L.U (j k) := by
        by_contra hn
        exact ha (Matrix.det_eq_zero_of_row_eq_zero k fun i => dif_neg hn)
      have := hk ht
      rw [← hπ k] at this
      exact this
    refine ⟨h t₀, (mem_basicOpen_iff h U hle M.det t₀).2 ?_, ?_⟩
    · rw [hM]
      simp only [hπ]
      exact ha
    · rw [← Scheme.Hom.comp_apply, hp, hxt]
  obtain ⟨w, hw, rfl⟩ := hmem
  let t : Sp K' := IsLocalRing.closedPoint K'
  have ht : x' t = p w := by
    rw [← Set.mem_singleton_iff, ← hx']
    exact ⟨t, rfl⟩
  obtain ⟨h, hh⟩ := exists_lift (O.ι ≫ p) x' ⟨w, hw⟩ t ht.symm
  have hO : (h ≫ O.ι) t ∈ O := (h t).2
  have hle : ⊤ ≤ (h ≫ O.ι) ⁻¹ᵁ U := (top_le_iff _ U t).2 (P.basicOpen_le _ hO)
  have hd := (mem_basicOpen_iff _ U hle M.det t).1 hO
  rw [hM] at hd
  refine Matrix.eq_zero_of_mulVec_eq_zero hd (funext fun k => ?_)
  have := hc ((h ≫ O.ι) ≫ π k) (j k) (by rw [Category.assoc, h3, Category.assoc, hh])
  simpa [Matrix.mulVec, dotProduct, mul_comm] using this

theorem linearIndependent_on_fibres_of_closedPoints :
    ∀ (G Z : Scheme.{0}) (π : Z ⟶ Sp ℤ) [LocallyOfFiniteType π] (f : G ⟶ Z) [Flat f] [LocallyOfFinitePresentation f] (L : LB G), L.IsLB → ∀ (r : ℕ) (s : Fin r → LB.Sec L), let P : Z → Prop := fun z => ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Z), Set.range x = {z} → ∀ c : Fin r → K, (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x → ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0; (∀ z, IsClosed ({z} : Set Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Z), Set.range x = {z} ∧ ∀ c : Fin r → K, (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x → ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0) → ∀ z, P z := by
  intro G Z π _ f _ _ L hL r s P h z
  let U : Z.Opens := ⟨{z | P z}, isOpen_setOf_linearIndependent_on_fibres G Z f L hL r s⟩
  have hU : U = ⊤ := (GlobalTheory.jacobson_closedPoints_tools_int Z π).2.2.1 U ⊤ fun y hy => by
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨K, _, x, hx, hz⟩ := h y hy
    intro K' _ _ x' hx' c hc
    exact geometric_of_field G Z f L r s y K x hx hz K' x' hx' c hc
  have : z ∈ U := by rw [hU]; trivial
  exact this

end GlobalTheory.FibreLinInd
end
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.PowSec
open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {Q : ZHPre ρ M U₀}

theorem spMap_id (Ω : Type) [Field Ω] : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := Spec.map_id _

theorem exists_origin (hU : (U₀ : Set M.Z).Nonempty) {a : Q.L.L.ι}
    (ha : ⊤ ≤ (M.pt ≫ eSec Q.G) ⁻¹ᵁ Q.L.L.U a) : ∃ ξ : Ω, ξ ^ ((S.r * S.N) ^ 2) = 1 ∧
      ∀ (c : S.J → Ω) (v : Ω), GV Q c a Ω (M.pt ≫ eSec Q.G) v →
        (c ⬝ᵥ S.ev 0) * (ξ * valF M.pt _ (Q.L.rig.s (fun _ => a)).val) ^ S.N = v := by
  have he : eSec Q.G ≫ Q.G.hom = 𝟙 M.Z := Over.w η[Q.G]
  obtain ⟨g, r, jP, h1, h2, h3, hj⟩ := exists_data' Q hU (M.pt ≫ eSec Q.G) (RingHom.id Ω)
    (by rw [spMap_id, Category.id_comp]; exact (Category.assoc _ _ _).trans ((congrArg (M.pt ≫ ·) he).trans
          (Category.comp_id _)))
  have : Mono Q.φ := (MorphismProperty.monomorphisms _).of_isPullback Q.cart.1.flip
    (inferInstanceAs (Mono U₀.ι))
  have h2' : (g ≫ pullback.snd _ _) ≫ U₀.ι = M.pt := by
    rw [Category.assoc, h2, spMap_id, Category.id_comp]
  obtain ⟨e', c1, c2⟩ : ∃ e' : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀, e' ≫ Q.φ = U₀.ι ≫ eSec Q.G ∧
      e' ≫ pullback.fst _ _ = Q.u₀ ≫ eSec ρ.P.A := by
    have c1 := PolBaseChange.eSec_comm Q.cart
    have c2 := PolBaseChange.eSec_comm (isGrpPullback_pullback ρ.P.A Q.u₀)
    exact ⟨_, c1, c2⟩
  have e1 : g = (g ≫ pullback.snd _ _) ≫ e' := by
    refine (cancel_mono Q.φ).1 (h1.trans (Eq.symm ((Category.assoc _ _ _).trans ?_)))
    refine (congrArg ((g ≫ pullback.snd _ _) ≫ ·) c1).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eSec Q.G) h2')
  have e2 : g ≫ pullback.fst ρ.P.A.hom Q.u₀ = spMap S.R.val.toRingHom ≫ eSec ρ.P.A := by
    refine (congrArg (· ≫ pullback.fst ρ.P.A.hom Q.u₀) e1).trans ((Category.assoc _ _ _).trans ?_)
    refine (congrArg ((g ≫ pullback.snd _ _) ≫ ·) c2).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eSec ρ.P.A) (Q.u₀_gen _ h2'))
  have ha' : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ Q.L.L.U a := h1 ▸ ha
  obtain ⟨ξ, hξ, hs⟩ := GlobalTheory.basis_value_at_origin o Ω S ρ Ω S.R.val.toRingHom r jP (h3.trans e2)
    ((top_le_preimage_iff _ _).1 (h3 ▸ hj))
  refine ⟨ξ, hξ, fun c v H => ?_⟩
  have e := H _ g r jP h1 h2 h3 hj
  have hw := Q.w_rig Ω g M.pt _ jP a h1 e2 ((top_le_preimage_iff _ _).1 hj) ((top_le_preimage_iff _ _).1 ha')
  simp only [hs, hw, zpow_natCast] at e
  refine mul_left_cancel₀ (pow_ne_zero S.N (val_unit_ne g (le_w Q hj ha') (Q.w.s (fun _ => jP, fun _ => a))))
    (Eq.trans ?_ e)
  rw [dotProduct, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  change _ = c l * (S.ev 0 l * _)
  ring

section Open
variable {W : M.Z.Opens} {j : Sp Ω ⟶ W.toScheme} (hj : j ≫ W.ι = M.pt)
include hj

theorem le_of_mem {z : W.toScheme} {V : W.toScheme.Opens} (hz : z ∈ V) : ⊤ ≤ j ⁻¹ᵁ V :=
  top_le_preimage_of_specializes (fun w => W.ι.isOpenEmbedding.isInducing.specializes_iff.1 (by
    rw [← Scheme.Hom.comp_apply, hj]; exact M.pt_specializes w _)) hz

theorem Reg.mem_O {z : W.toScheme} {F : ∀ (K : Type) [Field K], (Sp K ⟶ W.toScheme) → K} (h : Reg z F) :
    F Ω j ∈ M.O (W.ι z) := by
  obtain ⟨V, f, hz, hf⟩ := h
  rw [← hf Ω j (le_of_mem hj hz), ← NormGlue.valF_comp_appIso W.ι V f j, hj]
  exact RatModel.valF_mem_O (U := W.ι ''ᵁ V) ⟨z, hz, rfl⟩ _

theorem exists_unit_val (V : W.toScheme.Opens) (c : Ω)
    (h : ∀ z ∈ V, c ≠ 0 ∧ c ∈ M.O (W.ι z) ∧ c⁻¹ ∈ M.O (W.ι z)) :
    ∃ u : Γ(W.toScheme, V)ˣ, ⊤ ≤ j ⁻¹ᵁ V → valF j V u.val = c := by
  by_cases hV : ⊤ ≤ j ⁻¹ᵁ V
  swap
  · exact ⟨1, fun h => (hV h).elim⟩
  have hz : j (IsLocalRing.closedPoint Ω) ∈ V := hV trivial
  have hne : ((W.ι ''ᵁ V : M.Z.Opens) : Set M.Z).Nonempty := ⟨_, _, hz, rfl⟩
  obtain ⟨f, hf⟩ := (RatModel.mem_ringOn_iff_exists hne).1 ((RatModel.mem_ringOn (x := c)).2 (by
    rintro _ ⟨z, hz, rfl⟩; exact (h z hz).2.1))
  obtain ⟨f', hf'⟩ := (RatModel.mem_ringOn_iff_exists hne).1 ((RatModel.mem_ringOn (x := c⁻¹)).2 (by
    rintro _ ⟨z, hz, rfl⟩; exact (h z hz).2.2))
  have hu : IsUnit f := IsUnit.of_mul_eq_one f' (M.res_injective _ hne (by
    rw [map_mul, map_one, M.res_apply, M.res_apply, hf, hf', mul_inv_cancel₀ (h _ hz).1]))
  refine ⟨(hu.map (W.ι.appLE _ V (W.ι.preimage_image_eq V).ge).hom).unit, fun _ => ?_⟩
  refine (valR_appLE j W.ι _ hV f).trans ?_
  rw [hj]
  exact hf

end Open

theorem exists_local [ArithBase o Ω] (hS : S.Over₀ M U₀) {W : M.Z.Opens} (hW : (W : Set M.Z).Nonempty)
    {O : LB (Q.G.hom ⁻¹ᵁ W).toScheme} {τ : S.J → O.Sec} (hO : O.IsLB) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤)
    {b : S.J → S.J → Ω}
    (hp : ∀ (a : Q.L.L.ι) (k : O.ι) (K : Type) [Field K] (β : Ω →+* K) (h : Sp K ⟶ (Q.G.hom ⁻¹ᵁ W).toScheme),
      (h ≫ (Q.G.hom ⁻¹ᵁ W).ι) ≫ Q.G.hom = spMap β ≫ M.pt → ⊤ ≤ (h ≫ (Q.G.hom ⁻¹ᵁ W).ι) ⁻¹ᵁ Q.L.L.U a →
      ⊤ ≤ h ⁻¹ᵁ O.U k → ∃ v, Ratio Q (Q.G.hom ⁻¹ᵁ W).ι τ b a k K h v)
    (hA : ∀ z ∈ W, (∀ i, b i ⬝ᵥ S.ev 0 ∈ M.O z) ∧ ∃ i, b i ⬝ᵥ S.ev 0 ≠ 0 ∧ (b i ⬝ᵥ S.ev 0)⁻¹ ∈ M.O z)
    (a : Q.L.L.ι) (k : O.ι) :
    ∃ u : Γ((Q.G.hom ⁻¹ᵁ W).toScheme, LB.wchart Q.L.L (fun _ : Fin 1 => (Q.G.hom ⁻¹ᵁ W).ι) (fun _ => a) ⊓ O.U k)ˣ,
      ∀ (K : Type) [Field K] (β : Ω →+* K) (h : Sp K ⟶ (Q.G.hom ⁻¹ᵁ W).toScheme),
      (h ≫ (Q.G.hom ⁻¹ᵁ W).ι) ≫ Q.G.hom = spMap β ≫ M.pt → ⊤ ≤ (h ≫ (Q.G.hom ⁻¹ᵁ W).ι) ⁻¹ᵁ Q.L.L.U a →
      ⊤ ≤ h ⁻¹ᵁ O.U k → Ratio Q (Q.G.hom ⁻¹ᵁ W).ι τ b a k K h (valF h _ u.val) := by
  have := ArithBase.ded (o := o) (Ω := Ω)
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have := Q.semi.smooth
  have := Q.semi.geomConnected
  have : GeometricallyIntegral Q.G.hom := grpObj_geometricallyIntegral_of_smooth _ Q.G
  have := IsNormalScheme.of_pred hS.normal
  have := EndoExtend.isPreimmersion_pt M
  have := EndoExtend.flat_pt M
  set ν := (Q.G.hom ⁻¹ᵁ W).ι with hν
  let p := Q.G.hom ∣_ W
  have hp' : p ≫ W.ι = ν ≫ Q.G.hom := morphismRestrict_ι _ _
  have : GeometricallyIntegral p :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) (isPullback_morphismRestrict Q.G.hom W).flip ‹_›
  let j : Sp Ω ⟶ W.toScheme := IsOpenImmersion.lift W.ι M.pt (by
    rw [Scheme.Opens.range_ι]; exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hW))
  have hj : j ≫ W.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have sq : IsPullback (𝟙 _) j M.pt W.ι := .of_horiz_isIso_mono ⟨(Category.id_comp _).trans hj.symm⟩
  have : IsPreimmersion j := MorphismProperty.of_isPullback (P := @IsPreimmersion) sq ‹_›
  have : Flat j := MorphismProperty.of_isPullback (P := @Flat) sq ‹_›
  have : IsDominant j := ⟨dense_iff_inter_open.2 fun V hV ⟨z, hz⟩ =>
    ⟨_, le_of_mem hj (V := ⟨V, hV⟩) hz (x := IsLocalRing.closedPoint Ω) trivial, _, rfl⟩⟩
  have he₀ : eSec Q.G ≫ Q.G.hom = 𝟙 M.Z := Over.w η[Q.G]
  let e : W.toScheme ⟶ (Q.G.hom ⁻¹ᵁ W).toScheme := (isPullback_morphismRestrict Q.G.hom W).lift
    (𝟙 _) (W.ι ≫ eSec Q.G) (by
      exact (Category.id_comp _).trans ((Category.assoc _ _ _).trans ((congrArg (W.ι ≫ ·) he₀).trans
        (Category.comp_id _))).symm)
  have he : e ≫ p = 𝟙 _ := IsPullback.lift_fst _ _ _ _
  have he' : e ≫ ν = W.ι ≫ eSec Q.G := IsPullback.lift_snd _ _ _ _
  have : IsIntegral (pullback p j) :=
    GeometricallyIntegral.geometrically_isIntegral j _ _ (.of_hasPullback p j)
  let N := LB.div (LB.LinComb Q.L.L (K := Fin 1) (fun _ => ν) (fun _ => (S.N : ℤ))) O
  have hJ : (pullback.fst p j ≫ ν) ≫ Q.G.hom = pullback.snd p j ≫ M.pt := by
    rw [Category.assoc, ← hp', pullback.condition_assoc, hj]
  choose t ht using fun a : N.ι => exists_unit hS.ne hτ (hp (a.1 0) a.2) (pullback.fst p j) _ hJ
    (pullback.fst p j ⁻¹ᵁ N.U a) (fun _ hy => Set.mem_iInter.1 hy.1 0) (fun _ hy => hy.2)
  have hov : ∀ {K : Type} [Field K] (h : Sp K ⟶ pullback p j), ((h ≫ pullback.fst p j) ≫ ν) ≫ Q.G.hom =
      spMap (Spec.preimage (h ≫ pullback.snd p j)).hom ≫ M.pt := fun h => by
    rw [show spMap (Spec.preimage (h ≫ pullback.snd p j)).hom = h ≫ pullback.snd p j from Spec.map_preimage _,
      Category.assoc h _ M.pt, ← hJ]
    simp only [Category.assoc]
  obtain ⟨σ, hσ⟩ := GenericExtend.exists_unit_extend_of_generic W.toScheme _ Ω j
    ((isNormalScheme_iff_pred _).1 inferInstance) ‹_› ‹_› ‹_› p e N he inferInstance ‹_›
    (LB.isLB_div (LB.isLB_linComb Q.L.isLB _ _) hO) t (by
      rintro ⟨a, k⟩ ⟨a', k'⟩ K _ h h1 h2
      obtain ⟨a, rfl⟩ : ∃ jL, a = fun _ => jL := ⟨a 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
      obtain ⟨a', rfl⟩ : ∃ jL, a' = fun _ => jL := ⟨a' 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
      replace h1 := (top_le_preimage_iff _ _).2 h1
      replace h2 := (top_le_preimage_iff _ _).2 h2
      have a1 := of_le_wchart (le_preimage_mono _ inf_le_left h1) 0
      have a2 := of_le_wchart (le_preimage_mono _ inf_le_left h2) 0
      have k1 := le_preimage_mono _ inf_le_right h1
      have k2 := le_preimage_mono _ inf_le_right h2
      refine ((ht _ K h h1).unique hS.ne hτ (hov h) a1 k1 ((ht _ K h h2).chart a2 k2 a1 k1)).trans
        (congrArg (· * _) (Eq.symm ((val_div_g _ _ _ _ _ h1 h2).trans (congrArg (· * _) ?_))))
      exact val_linComb_g (I := Fin 1) _ _ _ _ _ _ a1 a2) (by
      intro a
      let h₀ : Sp Ω ⟶ pullback p j := pullback.lift (j ≫ e) (𝟙 _) (by simp [he])
      have hh₀ : h₀ ≫ pullback.fst p j = j ≫ e := pullback.lift_fst _ _ _
      have hh₁ : (j ≫ e) ≫ ν = M.pt ≫ eSec Q.G := by
        rw [Category.assoc, he']; exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eSec Q.G) hj)
      obtain ⟨u, hu⟩ := exists_unit_val hj (e ⁻¹ᵁ N.U a) (valF h₀ _ (t a).val) (fun z hz => by
        have m0 : ⊤ ≤ (j ≫ e) ⁻¹ᵁ N.U a := le_of_mem hj hz
        have H := ht a Ω h₀ (by rw [← hh₀] at m0; exact m0)
        rw [hh₀] at H
        have m1 := of_le_wchart (le_preimage_mono _ inf_le_left m0) 0
        obtain ⟨ξ, hξ, hv⟩ := exists_origin (Q := Q) hS.ne (a := a.1 0) (hh₁ ▸ m1)
        have hv' := fun i => hv _ _ (hh₁ ▸ H.2 i)
        have hn : (S.r * S.N) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.mul_ne_zero (by have := S.r_pos; omega)
          (by have := S.N_ge; omega))
        have hroot : ∀ x : Ω, x ^ ((S.r * S.N) ^ 2) = 1 → x ∈ M.O (W.ι z) := fun x hx => by
          have := RatModel.isIntegrallyClosed_O hS.normal (W.ι z)
          obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow (R := M.O (W.ι z))
            (Nat.pos_of_ne_zero hn) (hx ▸ isIntegral_one))
          exact hy ▸ y.2
        have m2 : W.ι z ∈ (Q.L.L.pull (eSec Q.G)).U (fun _ => a.1 0) := Set.mem_iInter.2 fun _ => by
          have : (e ≫ ν) z ∈ Q.L.L.U (a.1 0) := Set.mem_iInter.1 hz.1 0
          rw [he'] at this
          exact this
        have r1 := (Reg.val W.ι (Q.L.rig.s fun _ => a.1 0).val m2).mem_O hj
        have r2 := (Reg.inv W.ι (Q.L.rig.s fun _ => a.1 0).val (by
          rw [Scheme.basicOpen_of_isUnit _ (Units.isUnit _)]; exact m2)).mem_O hj
        have r3 := val_unit_ne M.pt (M.top_le_preimage_pt ⟨_, m2⟩) (Q.L.rig.s fun _ => a.1 0)
        simp only [hj] at r1 r2
        have x0 : ξ ≠ 0 := fun h => by rw [h, zero_pow hn] at hξ; exact zero_ne_one hξ
        obtain ⟨hA1, i', hA2, hA3⟩ := hA (W.ι z) z.2
        refine ⟨H.1, ?_, ?_⟩
        · obtain ⟨i, hi⟩ := exists_mem_basicOpen hτ (e z) hz.2
          have q : valF (j ≫ e) _ ((τ i).f a.2) ≠ 0 := ((le_preimage_basicOpen_iff (j ≫ e)
            (le_preimage_mono _ inf_le_right m0) _).1 (le_of_mem hj (V := e ⁻¹ᵁ Scheme.basicOpen _ ((τ i).f a.2)) hi)).ne_zero
          rw [(eq_mul_inv_iff_mul_eq₀ q).2 (hv' i).symm]
          exact mul_mem (mul_mem (hA1 i) (pow_mem (mul_mem (hroot ξ hξ) r1) _)) ((Reg.inv e _ hi).mem_O hj)
        · have q := mul_ne_zero hA2 (pow_ne_zero S.N (mul_ne_zero x0 r3))
          have key : ∀ A c t : Ω, A ≠ 0 → A = c * t → c⁻¹ = t * A⁻¹ := by
            rintro _ c t h rfl
            have := left_ne_zero_of_mul h
            have := right_ne_zero_of_mul h
            field_simp
          rw [key _ _ _ q (hv' i'), mul_inv, ← inv_pow, mul_inv]
          exact mul_mem ((Reg.val e _ hz.2).mem_O hj) (mul_mem hA3 (pow_mem (mul_mem
            (hroot _ (by rw [inv_pow, hξ, inv_one])) r2) _)))
      refine ⟨u, fun h hh hr => ?_⟩
      obtain rfl : h = h₀ := (cancel_mono (pullback.fst p j)).1 (hh.trans hh₀.symm)
      exact (hu ((top_le_preimage_iff (j ≫ e) _).2 hr)).symm)
  refine ⟨σ (fun _ => a, k), fun K _ β h h1 h2 h3 => ?_⟩
  obtain ⟨h, rfl⟩ : ∃ h' : Sp K ⟶ pullback p j, h' ≫ pullback.fst p j = h :=
    ⟨pullback.lift h (spMap β) ((cancel_mono W.ι).1 (by
      rw [Category.assoc, Category.assoc, hp', hj, ← h1, Category.assoc])), pullback.lift_fst _ _ _⟩
  have m : ⊤ ≤ (h ≫ pullback.fst p j) ⁻¹ᵁ N.U (fun _ => a, k) := le_inf' (le_wchart _ _ _ fun _ => h2) h3
  have := ht (fun _ => a, k) K h m
  rw [← hσ _ K h ((top_le_preimage_iff _ _).1 m)] at this
  exact this

theorem exists_pack [ArithBase o Ω] (hS : S.Over₀ M U₀) {EE : M.Lat S.J} (hQ : Q.SecO EE) {W : M.Z.Opens}
    (haff : IsAffineOpen W) (hW : (W : Set M.Z).Nonempty) {b : Matrix S.J S.J Ω} {d : Ω} (hd : d ≠ 0)
    (hb : ∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range b))
    (hA : ∀ z ∈ W, (∀ i, (b i ⬝ᵥ S.ev 0) / d ∈ M.O z) ∧
      ∃ i, (b i ⬝ᵥ S.ev 0) / d ≠ 0 ∧ ((b i ⬝ᵥ S.ev 0) / d)⁻¹ ∈ M.O z) :
    ∃ (O : LB (Q.G.hom ⁻¹ᵁ W).toScheme) (τ : S.J → O.Sec), O.IsLB ∧ ⨆ i, nonzeroLocus (τ i) = ⊤ ∧
      (∀ (a : Q.L.L.ι) (k : O.ι), ∃ u : Γ((Q.G.hom ⁻¹ᵁ W).toScheme,
          LB.wchart Q.L.L (fun _ : Fin 1 => (Q.G.hom ⁻¹ᵁ W).ι) (fun _ => a) ⊓ O.U k)ˣ,
        ∀ (K : Type) [Field K] (β : Ω →+* K) (h : Sp K ⟶ (Q.G.hom ⁻¹ᵁ W).toScheme),
        (h ≫ (Q.G.hom ⁻¹ᵁ W).ι) ≫ Q.G.hom = spMap β ≫ M.pt → ⊤ ≤ (h ≫ (Q.G.hom ⁻¹ᵁ W).ι) ⁻¹ᵁ Q.L.L.U a →
        ⊤ ≤ h ⁻¹ᵁ O.U k →
        Ratio Q (Q.G.hom ⁻¹ᵁ W).ι τ (fun i l => b i l / d) a k K h (valF h _ u.val)) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W → ∀ c : S.J → K,
        (∀ (g : Sp K ⟶ (Q.G.hom ⁻¹ᵁ W).toScheme) (k : O.ι), (g ≫ (Q.G.hom ⁻¹ᵁ W).ι) ≫ Q.G.hom = x →
          ∑ i, c i * valF g _ ((τ i).f k) = 0) → c = 0 := by
  obtain ⟨O, τ, hO, hτ, hp, hind, -⟩ := hQ W b haff hb
  refine ⟨O, τ, hO, hτ, exists_local hS hW hO hτ (fun a k K _ β h h1 h2 h3 => ?_) (fun z hz => ?_), ?_⟩
  · obtain ⟨g, r, jP, g1, g2, g3, gj⟩ := exists_data' Q hS.ne _ β h1
    obtain ⟨c, hc, H⟩ := hp K β g h r jP k g2 g1.symm g3 ((top_le_preimage_iff _ _).1 gj)
      ((top_le_preimage_iff _ _).1 h3)
    have z1 := zpow_ne_zero (S.N : ℤ) (val_unit_ne g (le_w Q gj (g1 ▸ h2)) (Q.w.s (fun _ => jP, fun _ => a)))
    have z2 : β d ≠ 0 := (map_ne_zero β).2 hd
    refine ⟨c / β d / _, div_ne_zero (div_ne_zero hc z2) z1, fun i => GV.of_one h2 g1 g2 g3 gj ?_⟩
    simp only [map_div₀, div_mul_eq_mul_div, ← Finset.sum_div, H]
    field_simp
  · have e : ∀ i, (fun l => b i l / d) ⬝ᵥ S.ev 0 = (b i ⬝ᵥ S.ev 0) / d := fun i => by
      simp only [dotProduct, div_mul_eq_mul_div, Finset.sum_div]
    simpa only [e] using hA z hz
  · intro K _ _ x hx c hc
    have := ArithBase.ft (o := o) (Ω := Ω)
    have := MinorModel.locallyOfFiniteType_int M
    have := jacobsonSpace_of_locallyOfFiniteType_int (M.s ≫ spMap (algebraMap ℤ o))
    have := Q.semi.smooth
    have hp' : Q.G.hom ∣_ W ≫ W.ι = (Q.G.hom ⁻¹ᵁ W).ι ≫ Q.G.hom := morphismRestrict_ι _ _
    let e := Fintype.equivFin S.J
    have hl : ∀ {K : Type} [Field K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W → ∃ x' : Sp K ⟶ W.toScheme, x' ≫ W.ι = x :=
      fun x hx => ⟨IsOpenImmersion.lift W.ι x (by rwa [Scheme.Opens.range_ι]), IsOpenImmersion.lift_fac _ _ _⟩
    have hr : ∀ {K : Type} [Field K] (x : Sp K ⟶ W.toScheme), Set.range x = {x (IsLocalRing.closedPoint K)} :=
      fun x => Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, rfl⟩, by
        rintro _ ⟨w, rfl⟩; exact congrArg x (Subsingleton.elim (α := PrimeSpectrum _) _ _)⟩
    obtain ⟨x, rfl⟩ := hl x hx
    have key := FibreLinInd.linearIndependent_on_fibres_of_closedPoints _ _
      (W.ι ≫ M.s ≫ spMap (algebraMap ℤ o)) (Q.G.hom ∣_ W) O hO _ (fun i => τ (e.symm i)) (fun z hz => by
        have h1 : IsClosed ({W.ι z} : Set M.Z) := isClosed_singleton_of_isLocallyClosed_singleton (by
          have := hz.isLocallyClosed.image W.ι.isOpenEmbedding.isInducing
            W.ι.isOpenEmbedding.isOpen_range.isLocallyClosed
          rwa [Set.image_singleton] at this)
        obtain ⟨K, _, y, hy, H⟩ := hind (W.ι z) z.2 h1
        obtain ⟨y, rfl⟩ := hl y (by rw [hy]; exact Set.singleton_subset_iff.2 z.2)
        have h2 : y (IsLocalRing.closedPoint K) = z := W.ι.isOpenEmbedding.injective
          (show (y ≫ W.ι) _ ∈ ({W.ι z} : Set M.Z) from hy ▸ ⟨_, rfl⟩)
        refine ⟨K, inferInstance, y, h2 ▸ hr y, fun c hc => ?_⟩
        have := H (c ∘ e) fun g k hg => by
          rw [← hc g k ((cancel_mono W.ι).1 (by rw [Category.assoc, hp', hg])), ← e.sum_comp]
          simp only [Function.comp_apply, Equiv.symm_apply_apply]
        exact funext fun i => by simpa using congrFun this (e.symm i)) _ K x (hr x) (c ∘ e.symm) (fun g k hg => by
        rw [← hc g k (by rw [Category.assoc, ← hp', ← Category.assoc, hg])]
        exact e.symm.sum_comp fun i => c i * valF g _ ((τ i).f k))
    exact funext fun i => by simpa using congrFun key (e i)

theorem exists_sections : GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → S.IsEE M U₀ EE → Q.SecO EE → ∀ (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b)) → ∃ σ : S.J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))).U j), (∀ i, σ i ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) ∧ GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W → (∀ g : Sp K ⟶ Q.G.left, g ≫ Q.G.hom = x → ∃ i j, valF g _ (σ i j) ≠ 0) ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ Q.G.left) (j : _), g ≫ Q.G.hom = x → ∑ i, c i * valF g _ (σ i j) = 0) → c = 0 := by
  intro h1 h2 h3 h4 h5 o Ω _ _ _ _ S ρ M U₀ EE Q hS hE hQ W x₀ b hb
  have hloc := fun (z : M.Z) (hz : z ∈ W) => (exists_isAffineOpen_mem_and_subset hz).imp
    fun W' (h : IsAffineOpen W' ∧ z ∈ W' ∧ (W' : Set M.Z) ⊆ W) => And.intro h (exists_pack hS hQ h.1 ⟨z, h.2.1⟩
      (hb z hz).1.1 (fun y hy => (hb y (h.2.2 hy)).2) fun y hy =>
        basis_origin_values_regular_and_unit h1 h2 h3 h4 h5 o Ω S ρ M U₀ EE hS hE y x₀ b (hb y (h.2.2 hy)).1
          (hb y (h.2.2 hy)).2)
  obtain ⟨F, _, β, g, r, jP, g2, -, -, hξ⟩ := Q.exists_generic hS.ne
  have hβ : (g ≫ Q.φ) ≫ Q.G.hom = spMap β ≫ M.pt := by
    rw [Category.assoc, Q.cart.1.w]; exact g2
  generalize g ≫ Q.φ = ξ at hξ hβ
  clear g2 g r jP
  have hid : ∀ {K : Type} [Field K] {g : Sp K ⟶ Q.G.left} {j : Fin 1 → Q.L.L.ι},
      ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ W ⊓ LB.wchart Q.L.L (fun _ => 𝟙 Q.G.left) j) → ⊤ ≤ g ⁻¹ᵁ Q.L.L.U (j 0) :=
    fun h _ hz => Set.mem_iInter.1 (h hz).2 0
  choose σ hσ using fun (i : S.J) (j : Fin 1 → Q.L.L.ι) =>
    exists_glue (Q.G.hom ⁻¹ᵁ W ⊓ LB.wchart Q.L.L (fun _ => 𝟙 Q.G.left) j)
      (GV Q (fun l => b i l / S.th x₀) (j 0)) ξ hξ (fun h v v' H H' => H.unique hS.ne hβ (hid h) H')
      (fun y hy => by
        obtain ⟨W', ⟨-, hz, -⟩, O, τ, hO, -, hu, -⟩ := hloc _ hy.1
        let y' : (Q.G.hom ⁻¹ᵁ W').toScheme := ⟨y, hz⟩
        obtain ⟨k, hk⟩ := exists_chart hO y'
        obtain ⟨u, hu⟩ := hu (j 0) k
        have hy' : y' ∈ LB.wchart Q.L.L (fun _ : Fin 1 => (Q.G.hom ⁻¹ᵁ W').ι) (fun _ => j 0) ⊓ O.U k :=
          ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.2 0, hk⟩
        refine ⟨_, ((Q.G.hom ⁻¹ᵁ W').ι.appIso _).inv.hom (u.val * resG _ inf_le_right ((τ i).f k)),
          ⟨y', hy', rfl⟩, fun K _ g q1 q2 => ?_⟩
        obtain ⟨h, rfl⟩ : ∃ h : Sp K ⟶ (Q.G.hom ⁻¹ᵁ W').toScheme, h ≫ (Q.G.hom ⁻¹ᵁ W').ι = g :=
          ⟨IsOpenImmersion.lift _ g (by
            rintro _ ⟨w, rfl⟩
            obtain ⟨v, -, hv⟩ := q1 (x := w) trivial
            exact ⟨v, hv⟩), IsOpenImmersion.lift_fac _ _ _⟩
        rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq] at q1
        rw [NormGlue.valF_comp_appIso]
        intro β' g' r' jP' k1 k2 k3 kj
        refine ((hu K β' h (by rw [← k1, Category.assoc, Q.cart.1.w]; exact k2) (hid q2)
          (le_preimage_mono h inf_le_right q1)).2 i β' g' r' jP' k1 k2 k3 kj).trans (congrArg (_ * ·) ?_)
        exact ((valR_mul h _ q1 _ _).trans (congrArg (_ * ·) (valR_res h _ q1 _))).symm)
  refine ⟨σ, fun i => ⟨fun j j' => eq_of_valF_generic ξ hξ fun h => ?_, ?_⟩, fun K _ _ x hx => ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ a, j = fun _ => a := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
    obtain ⟨a', rfl⟩ : ∃ a, j' = fun _ => a := ⟨j' 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
    have q1 := le_preimage_mono ξ inf_le_left h
    have q2 := le_inf' (le_preimage_mono ξ inf_le_left q1) (le_preimage_mono ξ inf_le_right h)
    refine (valR_res ξ _ h _).trans (Eq.trans ?_ ((valR_mul ξ _ h _ _).trans
      (congrArg₂ (· * ·) (valR_res ξ _ h _) (valR_res ξ _ h _))).symm)
    refine ((hσ i _ F ξ q1).unique hS.ne hβ (hid q1) ((hσ i _ F ξ q2).chart (hid q2) (hid q1))).trans
      (congrArg (· * _) ?_)
    exact (val_linComb_g (I := Fin 1) Q.L.L (𝟙 _) _ a a' ξ (hid q1) (hid q2)).symm
  · intro K _ β' g r jP jL k1 k2 k3 k4 k5
    exact hσ i (fun _ => jL) K _ (le_inf' ((top_le_preimage_iff _ _).2 k5)
      (le_wchart _ _ _ fun _ => (top_le_preimage_iff _ _).2 k4)) β' g r jP rfl k1 k2 ((top_le_preimage_iff _ _).2 k3)
  · obtain ⟨W', ⟨-, hz, hle⟩, O, τ, hO, hτ, hu, hind⟩ := hloc _ (hx ⟨IsLocalRing.closedPoint K, rfl⟩)
    have hx' : ⊤ ≤ x ⁻¹ᵁ W' := (le_preimage_iff x _).2 hz
    have hne : genericPoint Q.G.left ∈ Q.G.hom ⁻¹ᵁ W' := by
      change Q.G.hom _ ∈ W'
      rw [Q.hom_genericPoint]
      exact (genericPoint_specializes _).mem_open W'.isOpen hz
    have : Nonempty (Q.G.hom ⁻¹ᵁ W').toScheme := ⟨⟨_, hne⟩⟩
    have : IsIntegral (Q.G.hom ⁻¹ᵁ W').toScheme := isIntegral_of_isOpenImmersion (Q.G.hom ⁻¹ᵁ W').ι
    obtain ⟨ξ, rfl⟩ : ∃ h : Sp F ⟶ (Q.G.hom ⁻¹ᵁ W').toScheme, h ≫ (Q.G.hom ⁻¹ᵁ W').ι = ξ :=
      ⟨IsOpenImmersion.lift _ ξ (by
        rintro _ ⟨w, rfl⟩
        exact ⟨⟨_, hne⟩, (hξ w).symm⟩), IsOpenImmersion.lift_fac _ _ _⟩
    have hξ' : ∀ w, ξ w = genericPoint _ := fun w => (Q.G.hom ⁻¹ᵁ W').ι.isOpenEmbedding.injective
      ((hξ w).trans (genericPoint_eq_of_isOpenImmersion _).symm)
    have hrel : ∀ (a : Q.L.L.ι) (k : O.ι) (h : Sp K ⟶ (Q.G.hom ⁻¹ᵁ W').toScheme),
        ⊤ ≤ (h ≫ (Q.G.hom ⁻¹ᵁ W').ι) ⁻¹ᵁ Q.L.L.U a → ⊤ ≤ h ⁻¹ᵁ O.U k → ∃ v : K, v ≠ 0 ∧ ∀ i,
          valF (h ≫ (Q.G.hom ⁻¹ᵁ W').ι) _ (σ i fun _ => a) = v * valF h _ ((τ i).f k) := fun a k h q1 q2 => by
      obtain ⟨u, hu⟩ := hu a k
      have q := le_inf' (le_wchart Q.L.L _ (fun _ : Fin 1 => a) fun _ => q1) q2
      have hl : LB.wchart Q.L.L (fun _ : Fin 1 => (Q.G.hom ⁻¹ᵁ W').ι) (fun _ => a) ⊓ O.U k ≤ (Q.G.hom ⁻¹ᵁ W').ι ⁻¹ᵁ
          (Q.G.hom ⁻¹ᵁ W ⊓ LB.wchart Q.L.L (fun _ : Fin 1 => 𝟙 Q.G.left) fun _ => a) := fun y hy =>
        ⟨hle y.2, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 0⟩
      refine ⟨_, val_unit_ne h q u, fun i => ?_⟩
      have e : ((Q.G.hom ⁻¹ᵁ W').ι.appLE _ _ hl).hom (σ i fun _ => a) = u.val * resG _ inf_le_right ((τ i).f k) :=
        eq_of_valF_generic ξ hξ' fun q => by
          have q' := le_preimage_comp ξ _ hl q
          refine (valR_appLE ξ _ hl q _).trans (Eq.trans ?_
            ((valR_mul ξ _ q _ _).trans (congrArg (_ * ·) (valR_res ξ _ q _))).symm)
          exact (hσ i _ F _ q').unique hS.ne hβ (hid q')
            ((hu F β ξ hβ (hid q') (le_preimage_mono ξ inf_le_right q)).2 i)
      exact (valR_appLE h _ hl q _).symm.trans ((congrArg (valR h _) e).trans
        ((valR_mul h _ q _ _).trans (congrArg (_ * ·) (valR_res h _ q _))))
    refine ⟨fun g hg => ?_, fun c hc => hind K x ((top_le_preimage_iff _ _).1 hx') c fun g k hg => ?_⟩
    · subst hg
      obtain ⟨h, rfl⟩ : ∃ h : Sp K ⟶ (Q.G.hom ⁻¹ᵁ W').toScheme, h ≫ (Q.G.hom ⁻¹ᵁ W').ι = g :=
        ⟨IsOpenImmersion.lift _ g (by
          rintro _ ⟨w, rfl⟩
          exact ⟨⟨_, hx' (x := w) trivial⟩, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩
      obtain ⟨a, ha⟩ := exists_le_preimage_of_iSup_eq_top (h ≫ (Q.G.hom ⁻¹ᵁ W').ι) Q.L.isLB.cover
      obtain ⟨k, hk⟩ := exists_le_preimage_of_iSup_eq_top h hO.cover
      obtain ⟨v, hv, H⟩ := hrel a k h ha hk
      obtain ⟨i, hi⟩ := exists_ne hτ h hk
      exact ⟨i, fun _ => a, (H i).trans_ne (mul_ne_zero hv hi)⟩
    · by_cases hk : ⊤ ≤ g ⁻¹ᵁ O.U k
      · obtain ⟨a, ha⟩ := exists_le_preimage_of_iSup_eq_top (g ≫ (Q.G.hom ⁻¹ᵁ W').ι) Q.L.isLB.cover
        obtain ⟨v, hv, H⟩ := hrel a k g ha hk
        refine mul_left_cancel₀ hv ((Finset.mul_sum _ _ _).trans (Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
          ((hc _ (fun _ => a) hg).trans (mul_zero v).symm)))
        exact (mul_left_comm _ _ _).trans (congrArg (c i * ·) (H i).symm)
      · exact Finset.sum_eq_zero fun i _ => by rw [val_junk g hk, mul_zero]

end GlobalTheory.ZH.PowSec
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_pow_line_bundle_from_local_basis : GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → S.IsEE M U₀ EE → Q.SecO EE → ∀ (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b)) → ∃ σ : S.J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))).U j), (∀ i, σ i ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) ∧ GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W → (∀ g : Sp K ⟶ Q.G.left, g ≫ Q.G.hom = x → ∃ i j, valF g _ (σ i j) ≠ 0) ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ Q.G.left) (j : _), g ≫ Q.G.hom = x → ∑ i, c i * valF g _ (σ i j) = 0) → c = 0 := by
  atlas_forward_decl GlobalTheory.ZH.PowSec.exists_sections
end
