import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSchemeCubicalBundleExistsAndMapsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenThetaAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSymmetricVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LbIsoPwPullPowLocal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsFiniteOfPullVeryAmpleIsoPow
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankTotalDegreeImageGrowth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFormEqHighPowerSectionStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwich
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.VeryAmpleGrowth

variable {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))

theorem top_add {M : LB X} (a b : SecOnR f M ⊤) (k : M.ι) :
    (SecOnR.topEquiv f M (a + b)).f k = (SecOnR.topEquiv f M a).f k + (SecOnR.topEquiv f M b).f k := by
  rw [SecOnR.topEquiv_f, SecOnR.topEquiv_f, SecOnR.topEquiv_f, SecOnR.coord_add, map_add]

theorem top_smul {M : LB X} (c : K) (a : SecOnR f M ⊤) (k : M.ι) :
    (SecOnR.topEquiv f M (c • a)).f k = cst f (M.U k) c * (SecOnR.topEquiv f M a).f k := by
  rw [SecOnR.topEquiv_f, SecOnR.topEquiv_f, SecOnR.coord_base_smul, map_mul, rs_cst]

theorem top_ext {M : LB X} {a b : SecOnR f M ⊤}
    (h : ∀ k, (SecOnR.topEquiv f M a).f k = (SecOnR.topEquiv f M b).f k) : a = b :=
  (SecOnR.topEquiv f M).injective (by
    generalize SecOnR.topEquiv f M a = x at h ⊢
    generalize SecOnR.topEquiv f M b = y at h ⊢
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    obtain rfl : x = y := funext h
    rfl)

theorem top_zero {M : LB X} (k : M.ι) : (SecOnR.topEquiv f M 0).f k = 0 := by
  rw [SecOnR.topEquiv_f, SecOnR.coord_zero, map_zero]

def linTop {M : LB X} {V : Type} [AddCommGroup V] [Module K V] (φ : V → LB.Sec M)
    (hadd : ∀ a b k, (φ (a + b)).f k = (φ a).f k + (φ b).f k)
    (hsmul : ∀ (c : K) a k, (φ (c • a)).f k = cst f (M.U k) c * (φ a).f k) :
    V →ₗ[K] SecOnR f M ⊤ where
  toFun a := (SecOnR.topEquiv f M).symm (φ a)
  map_add' a b := top_ext f fun k => by
    simp only [top_add, LinearEquiv.apply_symm_apply, hadd]
  map_smul' c a := top_ext f fun k => by
    simp only [top_smul, LinearEquiv.apply_symm_apply, hsmul, RingHom.id_apply]

theorem top_linTop {M : LB X} {V : Type} [AddCommGroup V] [Module K V] (φ : V → LB.Sec M) (hadd hsmul)
    (a : V) : SecOnR.topEquiv f M (linTop f φ hadd hsmul a) = φ a :=
  (SecOnR.topEquiv f M).apply_symm_apply _

def mulPw {H : LB X} (s : LB.Sec H) (t : ℕ) (σ : LB.Sec (pw H t)) : LB.Sec (pw H (t + 1 : ℕ)) where
  f := fun k => s.f k * (show Γ(X, H.U k) from σ.f k)
  compat := fun k l => by
    have h₁ : rs X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (s.f k) =
      (H.g k l).val * rs X (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) (s.f l) := s.compat k l
    have h₂ : rs X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (σ.f k) =
      (H.g k l ^ (t : ℤ)).val * rs X (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) (σ.f l) := σ.compat k l
    change rs X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (s.f k * (show Γ(X, H.U k) from σ.f k)) =
      (H.g k l ^ ((t + 1 : ℕ) : ℤ)).val *
        rs X (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) (s.f l * (show Γ(X, H.U l) from σ.f l))
    rw [map_mul, map_mul, h₁, h₂, zpow_natCast, zpow_natCast, pow_succ, Units.val_mul]
    ring

def mulLin {H : LB X} (s : LB.Sec H) (t : ℕ) :
    SecOnR f (pw H t) ⊤ →ₗ[K] SecOnR f (pw H (t + 1 : ℕ)) ⊤ :=
  linTop f (fun a => mulPw s t (SecOnR.topEquiv f _ a))
    (fun a b k => (congrArg (fun y : Γ(X, H.U k) => s.f k * y) (top_add f a b k)).trans
      (mul_add (s.f k) (show Γ(X, H.U k) from (SecOnR.topEquiv f (pw H t) a).f k)
        (show Γ(X, H.U k) from (SecOnR.topEquiv f (pw H t) b).f k)))
    (fun c a k => (congrArg (fun y : Γ(X, H.U k) => s.f k * y) (top_smul f c a k)).trans
      (mul_left_comm _ _ _))

theorem top_mulLin {H : LB X} (s : LB.Sec H) (t : ℕ) (a : SecOnR f (pw H t) ⊤) :
    SecOnR.topEquiv f (pw H (t + 1 : ℕ)) (mulLin f s t a) = mulPw s t (SecOnR.topEquiv f (pw H t) a) :=
  top_linTop f _ _ _ a

theorem mulLin_injective [IsIntegral X] {H : LB X} (s : LB.Sec H) {x : X} (hx : x ∈ nonzeroLocus s) (t : ℕ) :
    Function.Injective (mulLin f s t) := by
  obtain ⟨k₀, hk₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  let W : X.Opens := X.basicOpen (s.f k₀)
  have hWU : W ≤ H.U k₀ := X.basicOpen_le _
  haveI : Nonempty W := ⟨⟨x, hk₀⟩⟩
  have hu : IsUnit (rs X hWU (s.f k₀)) := X.toRingedSpace.isUnit_res_basicOpen _
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have h : s.f k₀ * (show Γ(X, H.U k₀) from (SecOnR.topEquiv f (pw H t) a).f k₀) = 0 := by
    have e := top_mulLin f s t a
    rw [ha] at e
    exact (congrArg (fun σ : LB.Sec (pw H (t + 1 : ℕ)) => σ.f k₀) e).symm.trans
      (top_zero f (M := pw H (t + 1 : ℕ)) k₀)
  have h' := congrArg (rs X hWU) h
  rw [map_mul, map_zero, hu.mul_right_eq_zero] at h'
  exact top_ext f fun k =>
    (SecGrowth.sec_eq_zero (M := pw H t) (SecOnR.topEquiv f _ a) (k₀ := k₀) hWU h' k).trans
      (top_zero f k).symm

theorem finite_of_polynomial {H : LB X} {m : ℕ} (s : Fin (m + 1) → LB.Sec H) (t : ℕ)
    (h : ∀ σ : LB.Sec (pw H t), ∃ F : MvPolynomial (Fin (m + 1)) K, F.IsHomogeneous t ∧
      ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) F) :
    Module.Finite K (SecOnR f (pw H t) ⊤) := by
  haveI : Module.Finite K (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K t) :=
    Submodule.finiteDimensional_of_le (S₂ := MvPolynomial.restrictTotalDegree (Fin (m + 1)) K t)
      fun F hF => (MvPolynomial.mem_restrictTotalDegree _ _ _).2
        (MvPolynomial.IsHomogeneous.totalDegree_le hF)
  refine Module.Finite.of_surjective
    (linTop f (V := MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K t)
      (fun F => SecGrowth.polySec f s F.2)
      (fun a b k => map_add (MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k)) a.1 b.1)
      (fun c a k => ?_)) fun a => ?_
  · change MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) (c • a.1) =
      cst f (H.U k) c * MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) a.1
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C]
  · obtain ⟨F, hF, hFa⟩ := h (SecOnR.topEquiv f _ a)
    refine ⟨⟨F, hF⟩, top_ext f fun k => ?_⟩
    exact (congrArg (fun σ : LB.Sec (pw H t) => σ.f k) (top_linTop f _ _ _ _)).trans (hFa k).symm

theorem finite_monotone_growth : ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) ∧ (∀ t t' : ℕ, t ≤ t' → Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (f) (pw H t') ⊤)) ∧ ∃ c C : ℕ, 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ g ≤ c * Module.finrank K (SecOnR (f) (pw H t) ⊤) ∧ Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ C * t ^ g := by
  intro K _ X _ f g hf H n s hH hs
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.exists_homogeneousForm_eq_highPowerSection K X f H n s hH hs
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hx : x ∈ ⨆ i, nonzeroLocus (s i) := by rw [hs.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hinj := mulLin_injective f (s i) hi
  have hfin : ∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤) := fun t => by
    have h : ∀ d t : ℕ, t₀ ≤ t + d → Module.Finite K (SecOnR f (pw H t) ⊤) := by
      intro d
      induction d with
      | zero => exact fun t ht => finite_of_polynomial f s t (ht₀ t ht)
      | succ d ih =>
        intro t ht
        haveI := ih (t + 1) (by omega)
        exact Module.Finite.of_injective _ (hinj t)
    exact h t₀ t (Nat.le_add_left _ _)
  refine ⟨hfin, fun t t' h => ?_, ?_⟩
  · exact monotone_nat_of_le_succ (f := fun t : ℕ => Module.finrank K (SecOnR f (pw H t) ⊤))
      (fun t => LinearMap.finrank_le_finrank_of_injective (hinj t)) h
  · exact SecGrowth.growth_of_veryAmpleBy f s hs g t₀ ht₀
      (fun B _ _ _ r => finrank_totalDegree_image_growth K B _ _ r)
      (trdeg_eq_of_smoothOfRelativeDimension K X f g hf)
      (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR.topEquiv f _)
      (fun t a b k => top_add f a b k) (fun t c a k => top_smul f c a k)
      (fun t a ha => top_ext f fun k => (ha k).trans (top_zero f k).symm)
      (fun t σ => ⟨(SecOnR.topEquiv f _).symm σ, fun k => by rw [LinearEquiv.apply_symm_apply]⟩)

end GlobalTheory.VeryAmpleGrowth
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shift_finrank_sec_pull_bounds : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Etale φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  first | exact @GlobalTheory.finrank_sec_pull_sandwich | exact GlobalTheory.finrank_sec_pull_sandwich | (intros; apply GlobalTheory.finrank_sec_pull_sandwich <;> assumption)
end

section
namespace GlobalTheory.UU

theorem le_of_pow_le_poly_mul_pow (A B K a g : ℕ)
    (H : ∀ k, A ^ k ≤ K * B ^ k * (1 + k * a) ^ g) : A ≤ B := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · have := H 1
    simp [hB] at this
    omega
  by_contra hAB
  push Not at hAB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hr : (1 : ℝ) < (A : ℝ) / B := by
    rw [one_lt_div hBr]; exact_mod_cast hAB
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt g hr).const_mul
    ((K : ℝ) * (1 + a) ^ g)
  rw [mul_zero] at ht
  have h1 : ∀ᶠ k : ℕ in Filter.atTop,
      (1 : ℝ) ≤ ((K : ℝ) * (1 + a) ^ g) * ((k : ℝ) ^ g / ((A : ℝ) / B) ^ k) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hk' : A ^ k ≤ K * B ^ k * ((1 + a) * k) ^ g := by
      refine (H k).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
      nlinarith
    have hk2 : (A : ℝ) ^ k ≤ K * (B : ℝ) ^ k * ((1 + a) * k) ^ g := by exact_mod_cast hk'
    have hA : (0 : ℝ) < A := by exact_mod_cast (hB.trans hAB)
    rw [div_pow, ← mul_div_assoc, div_div_eq_mul_div, one_le_div (by positivity)]
    refine hk2.trans (le_of_eq ?_)
    rw [mul_pow]; ring
  have := ge_of_tendsto ht h1
  linarith

theorem degree_eq_pow_of_growth :
    ∀ (h : ℕ → ℕ) (g c C a d q : ℕ), 1 ≤ c → 1 ≤ q → (∀ t t', t ≤ t' → h t ≤ h t') → (∀ t, 1 ≤ t → t ^ g ≤ c * h t ∧ h t ≤ C * t ^ g) → (∀ t, d * h t ≤ h (q * (t + a)) ∧ h (q * t) ≤ d * h (t + a)) → d = q ^ g := by
  intro h g c C a d q hc hq hm hg hd
  have h1 : 1 ≤ h 1 := by
    have := (hg 1 le_rfl).1
    rcases Nat.eq_zero_or_pos (h 1) with h0 | h0
    · simp [h0] at this
    · exact h0
  have up : ∀ k t, h (q ^ k * t) ≤ d ^ k * h (t + k * a) := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      have e1 : q ^ (k + 1) * t = q ^ k * (q * t) := by ring
      rw [e1]
      refine (ih _).trans ?_
      rw [pow_succ, mul_assoc]
      refine Nat.mul_le_mul_left _ ?_
      have e2 : t + (k + 1) * a = t + k * a + a := by ring
      rw [e2]
      refine le_trans (hm _ _ ?_) (hd (t + k * a)).2
      rw [mul_add]
      exact Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hq) _
  have lo : ∀ k, d ^ k ≤ h (q ^ k * (1 + k * a)) := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih =>
      rw [pow_succ, mul_comm]
      refine (Nat.mul_le_mul_left d ih).trans ((hd _).1.trans (hm _ _ ?_))
      have hp : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
      have e : q ^ (k + 1) * (1 + (k + 1) * a) = q * (q ^ k * (1 + k * a) + q ^ k * a) := by ring
      rw [e]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hp) _)
  apply le_antisymm
  · apply le_of_pow_le_poly_mul_pow d (q ^ g) C a g
    intro k
    have hp : 1 ≤ q ^ k * (1 + k * a) := Nat.mul_pos (Nat.pow_pos hq) (by omega)
    refine (lo k).trans ((hg _ hp).2.trans (le_of_eq ?_))
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k g]; ring
  · apply le_of_pow_le_poly_mul_pow (q ^ g) d (c * C) a g
    intro k
    have hp : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
    have a1 := (hg _ hp).1
    have a2 := up k 1
    rw [mul_one] at a2
    have a3 := (hg (1 + k * a) (by omega)).2
    calc (q ^ g) ^ k = (q ^ k) ^ g := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ c * h (q ^ k) := a1
      _ ≤ c * (d ^ k * (C * (1 + k * a) ^ g)) :=
        Nat.mul_le_mul_left _ (a2.trans (Nat.mul_le_mul_left _ a3))
      _ = _ := by ring

end GlobalTheory.UU
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finrank_eq_card_kernel_points_of_etale :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ φ : B ⟶ B, ∀ [IsFinite φ.left] [Etale φ.left], ∀ x : B.left, φ.left.finrank x = Nat.card {y : 𝟙_ _ ⟶ B // y ≫ φ = 1} := by
  intro K _ _ B _ _ hB φ _ _ x
  have := hB.geomConnected
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
  let o : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B := 1
  let t : Spec (CommRingCat.of K) ⟶ B.left := o.left
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  have ht : t ≫ B.hom = 𝟙 _ := Over.w o
  rw [(Scheme.Hom.isLocallyConstant_finrank φ.left).apply_eq_of_preconnectedSpace x (t z),
    ← (GlobalTheory.FinEt.card_points_eq_finrank φ.left t z).2]
  refine Nat.card_congr
    { toFun := fun y ↦ ⟨Over.homMk y.1 ?_, Over.OverMorphism.ext y.2⟩
      invFun := fun y ↦ ⟨y.1.left, congrArg CommaMorphism.left y.2⟩
      left_inv := fun y ↦ rfl
      right_inv := fun y ↦ Subtype.ext (Over.OverMorphism.ext rfl) }
  change y.1 ≫ B.hom = 𝟙 _
  rw [← Over.w φ, ← Category.assoc, y.2, ht]

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UU.TorsionCount

theorem lbIso_pw {Y : Scheme.{0}} {A B : LB Y} (h : LBIso A B) (t : ℤ) : LBIso (AbLaw.pw A t) (AbLaw.pw B t) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨⟨fun p => w.s p ^ t⟩, fun p q => ?_⟩
  have e := congrArg (· ^ t) (hw p q)
  simp only [mul_zpow, ← map_zpow] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  exact (mul_zpow _ _ t).trans (congrArg₂ (· * ·) (map_zpow _ _ t).symm
    ((inv_zpow _ t).trans (congrArg (·⁻¹) (map_zpow _ _ t).symm)))

theorem pw_pw {X : Scheme.{0}} (H : LB X) (a b : ℤ) : AbLaw.pw (AbLaw.pw H a) b = AbLaw.pw H (a * b) := by
  unfold AbLaw.pw
  congr 1
  funext i j
  exact (zpow_mul _ _ _).symm

def chartPullPw {X Y : Scheme.{0}} (H : LB X) (φ : Y ⟶ X) (t : ℤ) :
    ChartPull ((AbLaw.pw H t).pull φ) (AbLaw.pw (H.pull φ) t) (𝟙 Y) where
  idx j := j
  le _ _ hy := hy
  g y i j hi hj :=
    (gm_pull_g (AbLaw.pw H t) φ (𝟙 Y) y i j hi hj).trans ((map_zpow _ _ t).trans
      ((congrArg (· ^ t) (gm_pull_g H φ (𝟙 Y) y i j hi hj).symm).trans (map_zpow _ _ t).symm))

theorem nonempty_secEquiv {K : Type} [CommRing K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (φ : X ⟶ X)
    (hφ : φ ≫ f = f) {H : LB X} (hH : H.IsLB) (q : ℕ) (h : LBIso (AbLaw.pw H q) (H.pull φ)) (t : ℕ) :
    Nonempty (SecOnR f (AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤ ≃ₗ[K] SecOnR (φ ≫ f) ((AbLaw.pw H t).pull φ) ⊤) := by
  have h₁ := (lbIso_pw h t).chartPull (chartPullId _) (chartPullPw H φ t)
  rw [pw_pw, ← Nat.cast_mul] at h₁
  obtain ⟨w, hw⟩ := h₁
  rw [hφ]
  exact ⟨SecOnR.linEquiv f (SecOn.congr (isLB_pw hH _) (pull_isLB (isLB_pw hH _) φ) w hw ⊤)⟩

theorem card_torsion_points : GlobalFnsSt → RigiditySt → (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) := by
  intro hG _ k _ _ B _ g n hB hg hn
  haveI := hB.comm
  haveI := hB.smooth
  haveI := hB.proper
  haveI : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  have hq : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hn0)
  have hproj := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k B hB
  obtain ⟨H, m, s, hH, hs, hsym⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmpleBy k B hB hproj
  obtain ⟨r, hr⟩ : ∃ r : LB.Gen (H.pull (eSec B)), r.IsGen :=
    DVR.exists_gen_of_isLB_local (V := k) _ (pull_isLB hH _)
  obtain ⟨M, hM⟩ := (GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps hG _ B hB).1 ⟨H, r, hH, hr⟩ (GlobalTheory.AbLaw.CubeProj.exists_gen_theta_abelianVariety hG k B hB hproj H hH) hsym
  have hiso : LBIso (AbLaw.pw H ((n ^ 2 : ℕ) : ℤ)) (H.pull (𝟙 B ^ n).left) := by
    have h := GlobalTheory.T.lbIso_pw_sq_pull_pow_of_isLocalRing k B M n
    rw [hM] at h
    rw [Nat.cast_pow]
    exact h
  have hφ : (𝟙 B ^ n).left ≫ B.hom = B.hom := Over.w _
  haveI : IsFinite (𝟙 B ^ n).left :=
    GlobalTheory.T.isFinite_of_pull_veryAmple_iso_pow k _ _ B.hom _ H H m s (n ^ 2) hH hH inferInstance (by rw [hφ]; exact hs) hq hiso
  haveI : Etale (𝟙 B ^ n).left := GrpTangent.etale_id_pow B (by
    simpa using (Ne.isUnit hn).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  have hcard := GlobalTheory.finrank_eq_card_kernel_points_of_etale k B hB (𝟙 B ^ n)
  have hc : Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} =
      Nat.card {y : 𝟙_ (Over (Sp k)) ⟶ B // y ≫ (𝟙 B ^ n) = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by rw [MonObj.comp_pow, Category.comp_id])
  rw [hc]
  obtain ⟨hfin, hmono, c, C, hc1, hgrow⟩ := GlobalTheory.VeryAmpleGrowth.finite_monotone_growth k B.left B.hom g hg H m s hH hs
  have e := nonempty_secEquiv B.hom _ hφ hH (n ^ 2) hiso
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_shift_finrank_sec_pull_bounds k B.left B.left B.hom (𝟙 B ^ n).left H m s hH hs _ hcard hfin fun t => by
    obtain ⟨e⟩ := e t
    haveI := hfin (n ^ 2 * t)
    exact Module.Finite.equiv e
  rw [pow_mul]
  refine GlobalTheory.UU.degree_eq_pow_of_growth (fun t : ℕ => Module.finrank k (SecOnR B.hom (AbLaw.pw H t) ⊤)) g c C a _ (n ^ 2) hc1 hq
    hmono hgrow fun t => ?_
  obtain ⟨e₁⟩ := e (t + a)
  obtain ⟨e₂⟩ := e t
  exact ⟨(ha t).1.trans e₁.finrank_eq.ge, e₂.finrank_eq.le.trans (ha t).2⟩

end GlobalTheory.UU.TorsionCount
end
end
