import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZH

attribute [local instance] SplitExt.free SplitExt.finite

theorem exists_chart_eq_top {k : Type} [Field k] {L : LB (Sp k)} (hL : L.IsLB) : ∃ i, L.U i = ⊤ := by
  have h : (default : Sp k) ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨i, top_le_iff.1 fun x _ => by rw [Subsingleton.elim x default]; exact hi⟩

theorem lbIso_of_chart_top {X : Scheme.{0}} {L M : LB X} (hL : L.IsLB) (i₀ : L.ι) (hi : L.U i₀ = ⊤)
    (hM : ∀ i j, M.g i j = 1) : LBIso L M := by
  have le : ∀ p : M.ι × L.ι, M.U p.1 ⊓ L.U p.2 ≤ L.U p.2 ⊓ L.U i₀ := fun p =>
    le_inf inf_le_right (by rw [hi]; exact le_top)
  refine ⟨⟨fun p => (res (le p) (L.g p.2 i₀))⁻¹⟩, fun (p q : M.ι × L.ι) => ?_⟩
  have le3 : M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ≤ L.U p.2 ⊓ L.U q.2 ⊓ L.U i₀ :=
    le_inf (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) (by rw [hi]; exact le_top)
  have e := congrArg (res le3) (hL.cocycle p.2 q.2 i₀)
  rw [map_mul, DVR.res_res', DVR.res_res', DVR.res_res'] at e
  show res (X := X) (U := M.U p.1 ⊓ L.U p.2) (V := M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2)) _
      (res (le p) (L.g p.2 i₀))⁻¹ =
    res (X := X) (V := M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2)) _ (M.g p.1 q.1) * (res _ (L.g p.2 q.2))⁻¹ *
      res (X := X) (U := M.U q.1 ⊓ L.U q.2) _ (res (le q) (L.g q.2 i₀))⁻¹
  rw [hM, map_one, map_inv, map_inv]
  erw [DVR.res_res', DVR.res_res', ← e, _root_.one_mul, mul_inv]
  rfl

section Torus
variable (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

theorem exists_torus_datum : ∃ (O : X → RigLB (𝟙_ (Over (Sp k)))) (h₁ : _) (h₂ : _) (h₃ : _),
    Nonempty ((SplitExt.mk (𝟙_ (Over (Sp k))) (Diag.isAbelianScheme_unit _) X O h₁ h₂ h₃).GtDatum
      (splitTorus (Sp k) X)) := by
  have e : (toUnit (splitTorus (Sp k) X)).left = (splitTorus (Sp k) X).hom := by
    simpa using Over.w (toUnit (splitTorus (Sp k) X))
  have := Diag.isAffineHom_hom (Sp k) X
  obtain ⟨O, h₁, h₂, h₃, h⟩ := exists_gtDatum_of_splitTorus_extension (Sp k) X (splitTorus (Sp k) X)
    (𝟙_ (Over (Sp k))) (Diag.isAbelianScheme_unit _) (toUnit _) (𝟙 _) ⟨toUnit_unique _ _, toUnit_unique _ _⟩
    inferInstance (e ▸ Diag.flat_hom (Sp k) X) (e ▸ Diag.surjective_hom (Sp k) X)
    (e ▸ (inferInstance : QuasiCompact (splitTorus (Sp k) X).hom))
    (Diag.isPullback_toUnit_of_lift _ (toUnit_unique _ _) (fun h => by simpa using h)
      fun t _ => ⟨t, Category.comp_id _⟩)
  obtain ⟨d, -⟩ := h (Diag.isAbelianScheme_unit _)
  exact ⟨O, h₁, h₂, h₃, ⟨d⟩⟩

theorem linComb_g_eq_one {X Y : Scheme.{0}} {L : LB X} (hL : ∀ i j, L.g i j = 1) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j j' : (LB.LinComb L φ ε).ι) : (LB.LinComb L φ ε).g j j' = 1 :=
  Finset.prod_eq_one fun _ _ => by rw [hL]; erw [map_one, map_one]; exact one_zpow _

def torusExt : SplitExt (Sp k) :=
  SplitExt.mk (𝟙_ (Over (Sp k))) (Diag.isAbelianScheme_unit _) X (exists_torus_datum k X).choose
    (exists_torus_datum k X).choose_spec.choose (exists_torus_datum k X).choose_spec.choose_spec.choose
    (exists_torus_datum k X).choose_spec.choose_spec.choose_spec.choose

def torusFib : FibPre k where
  E := torusExt k X
  G := splitTorus (Sp k) X
  D := (exists_torus_datum k X).choose_spec.choose_spec.choose_spec.choose_spec.some
  N₀ := Out.Inh.trivLB _
  isLB := Out.Inh.trivLB_isLB _
  aff _ := isAffineOpen_top (Sp k)
  ch _ i := (exists_chart_eq_top (((torusExt k X).O ((torusExt k X).basis i)).isLB)).choose
  le _ := le_iInf fun i => (exists_chart_eq_top (((torusExt k X).O ((torusExt k X).basis i)).isLB)).choose_spec.ge

def torusPol (N : ℕ) : (torusFib k X).Pol N where
  PB := Out.Inh.zeroPolAV (Sp k)
  β := Iso.refl _
  hom := inferInstanceAs (IsMonHom (𝟙 (𝟙_ (Over (Sp k)))))
  c _ := toUnit _
  w₀ := lbIso_of_chart_top (Out.Inh.trivLB_isLB _) PUnit.unit rfl
    (linComb_g_eq_one (Out.Inh.linComb_triv_g _ _) _ _)
  wO α := lbIso_of_chart_top ((torusExt k X).O α).isLB _ (exists_chart_eq_top ((torusExt k X).O α).isLB).choose_spec
    (Out.Inh.linComb_triv_g _ _)
end Torus

section Good
variable (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

def torusSec (d : ℕ) (x : AddMonoidAlgebra Γ(Sp k, ⊤) X) : ((torusFib k X).H d).Sec where
  f l := Equiv.ofBijective _ ((torusFib k X).D.coord ((torusFib k X).ch l) _ ((torusFib k X).aff l)
    ((torusFib k X).le l)) x
  compat i j := by
    have e : ((torusFib k X).H d).g i j = 1 :=
      (congrArg (· ^ d) (map_one (pullU (torusFib k X).D.q.left _))).trans (one_pow d)
    rw [e, Units.val_one, _root_.one_mul]
    rfl

theorem wt_torusSec (d : ℕ) (x : AddMonoidAlgebra Γ(Sp k, ⊤) X) (α : X) (l) :
    (torusFib k X).wt (torusSec k X d x) α l = x.coeff α :=
  congrArg (fun y : AddMonoidAlgebra Γ(Sp k, ⊤) X => y.coeff α) (Equiv.symm_apply_apply _ x)

theorem constFn_id_bijective (R : Type) [CommRing R] : Function.Bijective (constFn (𝟙 (Sp R)) ⊤) := by
  have e : constFn (𝟙 (Sp R)) ⊤ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    funext a
    simp only [constFn, Scheme.Hom.appLE_eq_app, Scheme.Hom.id_app]
    exact congrArg (fun φ => CommRingCat.Hom.hom φ _) ((Sp R).presheaf.map_id _)
  rw [e]
  exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv


end Good

def squareForm : QuadraticMap ℤ ℤ ℝ := QuadraticMap.linMulLin (Algebra.linearMap ℤ ℝ) (Algebra.linearMap ℤ ℝ)

theorem squareForm_apply (x : ℤ) : squareForm x = ((x ^ 2 : ℤ) : ℝ) := by simp [squareForm, sq]


theorem short_squareForm_iff (r : ℕ) (α : ℤ) : Short squareForm (2 * r + 1) α ↔ -(r : ℤ) ≤ α ∧ α ≤ r := by
  simp only [Short, squareForm_apply, Int.cast_le, nsmul_eq_mul]
  push_cast
  have hr : (0 : ℤ) ≤ r := Int.natCast_nonneg r
  constructor
  · intro h
    have h₁ := h 1
    have h₂ := h (-1)
    constructor
    · by_contra hc
      have : α ≤ -r - 1 := by omega
      nlinarith
    · by_contra hc
      have : r + 1 ≤ α := by omega
      nlinarith
  · rintro ⟨h₁, h₂⟩ m
    rw [sq_le_sq]
    rcases lt_trichotomy m 0 with h | rfl | h
    · refine (abs_le.2 ⟨h₁, h₂⟩).trans (le_abs.2 (Or.inr ?_))
      nlinarith
    · simp
    · refine (abs_le.2 ⟨h₁, h₂⟩).trans (le_abs.2 (Or.inl ?_))
      nlinarith




example : ¬ Short squareForm 4 3 := fun h => by have := h (-1); simp only [squareForm_apply] at this; norm_num at this

example : Short squareForm 3 (-1) := (short_squareForm_iff 1 (-1)).2 (by norm_num)

example (k : Type) [Field k] :
    (torusFib k ℤ).supp (torusSec k ℤ 1 (AddMonoidAlgebra.single (1 : ℤ) 1)) = {(1 : ℤ)} := by
  have key : ∀ α : ℤ, α ∈ (torusFib k ℤ).supp (torusSec k ℤ 1 (AddMonoidAlgebra.single (1 : ℤ) 1)) ↔
      (AddMonoidAlgebra.single (1 : ℤ) (1 : Γ(Sp k, ⊤))).coeff α ≠ 0 := fun α =>
    ⟨fun ⟨l, hl⟩ h => hl ((wt_torusSec k ℤ 1 _ α l).trans h),
      fun h => ⟨PUnit.unit, fun h' => h ((wt_torusSec k ℤ 1 _ α PUnit.unit).symm.trans h')⟩⟩
  refine Set.ext fun α : ℤ => (key α).trans ?_
  show _ ↔ α = 1
  by_cases h : α = 1
  · simp [h]
  · simp [h, Finsupp.single_apply, Ne.symm h]

end GlobalTheory.ZH
end
