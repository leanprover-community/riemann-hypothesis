import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorPeriodDefectIsCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorPolynomialDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantFieldConstCoeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorFieldZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermChartFunctionsIsWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudFourierTermSubSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaShiftFunctionalEqSubConstFnSmul

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cocycle_polynomial_defect : ∀ (R X : Type) [CommRing R] [IsDomain R] [CharZero R] [AddCommGroup X] (w : X → X →+ R) (π π' : X → R), (∀ (k : ℕ), 1 ≤ k → ∀ mu mu' α : X, 2 * (k : R) * w (mu + mu') α + 2 * (k : R) ^ 2 * π (mu + mu') + 2 * (k : R) * π' (mu + mu') = (2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) + (2 * (k : R) * w mu' (α + k • mu) + 2 * (k : R) ^ 2 * π mu' + 2 * (k : R) * π' mu')) → (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) ∧ (∀ mu mu', w mu mu' = w mu' mu) ∧ (∀ mu mu', π' (mu + mu') = π' mu + π' mu') ∧ ∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu := by
  intro R X _ _ _ _ w π π' h
  have key : ∀ k : ℕ, 1 ≤ k → ∀ mu mu' α : X,
      2 * (k : R) * (w (mu + mu') α - w mu α - w mu' α)
        + 2 * (k : R) ^ 2 * (π (mu + mu') - π mu - π mu' - w mu' mu)
        + 2 * (k : R) * (π' (mu + mu') - π' mu - π' mu') = 0 := by
    intro k hk mu mu' α
    have e := h k hk mu mu' α
    simp only [map_add, map_nsmul, nsmul_eq_mul] at e
    linear_combination e
  have hAB : ∀ mu mu' : X, π (mu + mu') - π mu - π mu' - w mu' mu = 0 ∧
      π' (mu + mu') - π' mu - π' mu' = 0 := by
    intro mu mu'
    have h1 := key 1 le_rfl mu mu' 0
    have h2 := key 2 (by norm_num) mu mu' 0
    simp only [map_zero] at h1 h2
    push_cast at h1 h2
    have h4 : (4 : R) * (π (mu + mu') - π mu - π mu' - w mu' mu) = 0 := by
      linear_combination h2 - 2 * h1
    have hA : π (mu + mu') - π mu - π mu' - w mu' mu = 0 :=
      (mul_eq_zero.mp h4).resolve_left (by norm_num)
    refine ⟨hA, ?_⟩
    have h2' : (2 : R) * (π' (mu + mu') - π' mu - π' mu') = 0 := by
      linear_combination h1 - 2 * hA
    exact (mul_eq_zero.mp h2').resolve_left (by norm_num)
  have hw : ∀ mu mu' α : X, w (mu + mu') α = w mu α + w mu' α := by
    intro mu mu' α
    have e := key 1 le_rfl mu mu' α
    obtain ⟨hA, hB⟩ := hAB mu mu'
    push_cast at e
    have e2 : (2 : R) * (w (mu + mu') α - w mu α - w mu' α) = 0 := by
      linear_combination e - 2 * hA - 2 * hB
    have := (mul_eq_zero.mp e2).resolve_left (by norm_num)
    linear_combination this
  refine ⟨hw, ?_, ?_, ?_⟩
  · intro mu mu'
    have a := (hAB mu mu').1
    have b := (hAB mu' mu).1
    rw [add_comm mu' mu] at b
    linear_combination a - b
  · intro mu mu'
    linear_combination (hAB mu mu').2
  · intro mu mu'
    linear_combination (hAB mu mu').1

end GlobalTheory
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_polynomialDefect_bilinear_additive_parts : ∀ (R X : Type) [CommRing R] [IsDomain R] [CharZero R] [AddCommGroup X] (w : X → X →+ R) (π π' : X → R), (∀ (k : ℕ), 1 ≤ k → ∀ mu mu' α : X, 2 * (k : R) * w (mu + mu') α + 2 * (k : R) ^ 2 * π (mu + mu') + 2 * (k : R) * π' (mu + mu') = (2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) + (2 * (k : R) * w mu' (α + k • mu) + 2 * (k : R) ^ 2 * π mu' + 2 * (k : R) * π' mu')) → (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) ∧ (∀ mu mu', w mu mu' = w mu' mu) ∧ (∀ mu mu', π' (mu + mu') = π' mu + π' mu') ∧ ∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu := by
  atlas_forward_decl GlobalTheory.cocycle_polynomial_defect
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperator_period_defect_isCocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (c : ℕ → Dd.toPre.X → Dd.toPre.X → R), IsBasic Y h → HasDefect Y h c → ∀ (k : ℕ), 1 ≤ k → ∀ mu mu' α, c k (mu + mu') α = c k mu α + c k mu' (α + k • mu) := by
  first | exact @GlobalTheory.HeatDefect.defect_cocycle | exact GlobalTheory.HeatDefect.defect_cocycle | (intros; apply GlobalTheory.HeatDefect.defect_cocycle <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_invariantField_const_coeffs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ ℓ : Dd.toPre.X →+ R, ∃ c : Fin n → R, GlobalTheory.HeatMod.IsTorField Y (GlobalTheory.HeatMod.combF Y.H.hom dd c) ℓ := by
  first | exact @GlobalTheory.HeatMod.TorField.exists_isTorField | exact GlobalTheory.HeatMod.TorField.exists_isTorField | (intros; apply GlobalTheory.HeatMod.TorField.exists_isTorField <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatMod.TorTensor

theorem quad_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {κ : Type} [Fintype κ] {n : ℕ}
    (d : Fin n → S → S) (c : κ → Fin n → R) (w : κ → κ → R) (F : κ → S → S)
    (hF : ∀ s f, F s f = ∑ a, φ (c s a) * d a f) (hadd : ∀ s f g, F s (f + g) = F s f + F s g)
    (hmul : ∀ s r f, F s (φ r * f) = φ r * F s f) (f : S) :
    ∑ a, ∑ b, φ (∑ s, ∑ t, w s t * c s a * c t b) * d a (d b f) = ∑ s, ∑ t, φ (w s t) * F s (F t f) := by
  have h : ∀ s t, F s (F t f) = ∑ a, ∑ b, φ (c s a) * φ (c t b) * d a (d b f) := by
    intro s t
    have hs := map_sum (AddMonoidHom.mk' (F s) (hadd s)) (fun b => φ (c t b) * d b f) Finset.univ
    simp only [AddMonoidHom.mk'_apply] at hs
    rw [hF t f, hs, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hmul, hF, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp only [h, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ s, ∑ b, ∑ t, φ (w s t) * φ (c s a) * φ (c t b) * d a (d b f) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ s, ∑ a, ∑ b, ∑ t, φ (w s t) * φ (c s a) * φ (c t b) * d a (d b f) := Finset.sum_comm
    _ = ∑ s, ∑ a, ∑ t, ∑ b, φ (w s t) * φ (c s a) * φ (c t b) * d a (d b f) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ s, ∑ t, ∑ a, ∑ b, φ (w s t) * φ (c s a) * φ (c t b) * d a (d b f) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by simp only [_root_.mul_assoc]

theorem form_eq {R X : Type} [CommRing R] [AddCommGroup X] {κ : Type} [Fintype κ] (b : Module.Basis κ ℤ X)
    (w : X → X →+ R) (hw : ∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) (α : X) :
    ∑ s, ∑ t, w (b s) (b t) * ((b.repr α t : ℤ) : R) * ((b.repr α s : ℤ) : R) = w α α := by
  have h1 : ∀ (g : X →+ R), g α = ∑ s, g (b s) * ((b.repr α s : ℤ) : R) := by
    intro g
    conv_lhs => rw [← b.sum_repr α]
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  have h2 := h1 (AddMonoidHom.mk' (fun mu => w mu α) fun mu mu' => hw mu mu' α)
  simp only [AddMonoidHom.mk'_apply] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [h1 (w (b s)), Finset.sum_mul]

def twoPullConstantsRingHom {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) (W : Z.Opens) : R →+* Γ(Z, W) :=
  (s.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem base_constant_function_eq_torTensorConstantsRingHom {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) (W : Z.Opens) (r : R) :
    constFn s W r = twoPullConstantsRingHom s W r := rfl

theorem exists_quad : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ w : Dd.toPre.X → Dd.toPre.X →+ R, (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) → (∀ mu mu', w mu mu' = w mu' mu) → ∃ M : Matrix (Fin n) (Fin n) R, Mᵀ = M ∧ (∀ (α : Dd.toPre.X) (W : Y.H.left.Opens), (∃ V : Dd.toPre.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → ∀ f, IsWt Y α W f → GlobalTheory.HeatMod.quadF Y.H.hom dd M W f = constFn Y.H.hom W (w α α) * f) ∧ ∀ (U : Dd.toPre.P.A.left.Opens) (g : Γ(Dd.toPre.P.A.left, U)) (W : Y.H.left.Opens) (k : ℕ) (f : Γ(Y.H.left, W)), W ≤ Y.q.left ⁻¹ᵁ U → GlobalTheory.HeatMod.quadF Y.H.hom dd M W (pbT Y.q.left g W ^ k * f) = pbT Y.q.left g W ^ k * GlobalTheory.HeatMod.quadF Y.H.hom dd M W f := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd w hw hsymm
  let b := Module.Free.chooseBasis ℤ Dd.toPre.X
  let ℓ : Module.Free.ChooseBasisIndex ℤ Dd.toPre.X → Dd.toPre.X →+ R := fun s =>
    (Int.castAddHom R).comp (b.coord s).toAddMonoidHom
  have hℓ : ∀ s α, ℓ s α = ((b.repr α s : ℤ) : R) := fun s α => rfl
  choose c hc using fun s => GlobalTheory.T.exists_torus_invariantField_const_coeffs R Dd O oa Y n v dd hdd (ℓ s)
  have hmul : ∀ s W r f, combF Y.H.hom dd (c s) W (twoPullConstantsRingHom Y.H.hom W r * f) =
      twoPullConstantsRingHom Y.H.hom W r * combF Y.H.hom dd (c s) W f := by
    intro s W r f
    rw [(hc s).1.2.1 W le_top, ← base_constant_function_eq_torTensorConstantsRingHom, (hc s).2.1 W r, mul_zero, add_zero]
  have key : ∀ W f, quadF Y.H.hom dd (Matrix.of fun a a' => ∑ s, ∑ t, w (b s) (b t) * c s a * c t a') W f =
      ∑ s, ∑ t, twoPullConstantsRingHom Y.H.hom W (w (b s) (b t)) * combF Y.H.hom dd (c s) W (combF Y.H.hom dd (c t) W f) :=
    fun W f => quad_eq (twoPullConstantsRingHom Y.H.hom W) (fun a => dd a W) c (fun s t => w (b s) (b t))
      (fun s => combF Y.H.hom dd (c s) W) (fun _ _ => rfl) (fun s => (hc s).1.1 W le_top) (fun s => hmul s W) f
  refine ⟨Matrix.of fun a a' => ∑ s, ∑ t, w (b s) (b t) * c s a * c t a', ?_, ?_, ?_⟩
  · ext a a'
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    rw [hsymm (b t) (b s)]
    ring
  · intro α W hW f hf
    rw [key, base_constant_function_eq_torTensorConstantsRingHom, ← form_eq b w hw α, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [(hc t).2.2.1 α W hW f hf, base_constant_function_eq_torTensorConstantsRingHom, hmul, (hc s).2.2.1 α W hW f hf, base_constant_function_eq_torTensorConstantsRingHom, hℓ, hℓ, map_mul,
      map_mul]
    ring
  · intro U g W k f hW
    rw [key, key, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [(hc t).2.2.2 U g W k f hW, (hc s).2.2.2 U g W k _ hW]
    ring

end GlobalTheory.HeatMod.TorTensor
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_second_order_operator_of_character_form : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ w : Dd.toPre.X → Dd.toPre.X →+ R, (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) → (∀ mu mu', w mu mu' = w mu' mu) → ∃ M : Matrix (Fin n) (Fin n) R, Mᵀ = M ∧ (∀ (α : Dd.toPre.X) (W : Y.H.left.Opens), (∃ V : Dd.toPre.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → ∀ f, IsWt Y α W f → GlobalTheory.HeatMod.quadF Y.H.hom dd M W f = constFn Y.H.hom W (w α α) * f) ∧ ∀ (U : Dd.toPre.P.A.left.Opens) (g : Γ(Dd.toPre.P.A.left, U)) (W : Y.H.left.Opens) (k : ℕ) (f : Γ(Y.H.left, W)), W ≤ Y.q.left ⁻¹ᵁ U → GlobalTheory.HeatMod.quadF Y.H.hom dd M W (pbT Y.q.left g W ^ k * f) = pbT Y.q.left g W ^ k * GlobalTheory.HeatMod.quadF Y.H.hom dd M W f := by
  atlas_forward_decl GlobalTheory.HeatMod.TorTensor.exists_quad
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatMod

theorem isWt_fourierTerm : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Q.P.L.ι) (W : Y.H.left.Opens), (∃ V : Q.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → W ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α W (rsT (τ.f fun _ => j) W) := by
  intro R _ _ Q Ω _ _ _ oa Y k α σ τ hT j W _ hW
  exact GlobalTheory.Heat.TermWt.isWt_term Y k α σ τ hT (fun _ => j) W fun _ hx => Set.mem_iInter.2 fun _ => hW hx

end GlobalTheory.HeatMod
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raynaudFourierTerm_chartRestriction_isWeight : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Q.P.L.ι) (W : Y.H.left.Opens), (∃ V : Q.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → W ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α W (rsT (τ.f fun _ => j) W) := by
  atlas_forward_decl GlobalTheory.HeatMod.isWt_fourierTerm
end

section
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatMod

theorem valR_sub_const_mul {R S : Type} [CommRing R] [CommRing S] {X : Scheme.{0}} (p : X ⟶ Sp R) (φ : R →+* S)
    (x : Sp S ⟶ X) (hx : x ≫ p = spMap φ) (W : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (f g : Γ(X, W)) (r : R) :
    valR x W (f - constFn p W r * g) = valR x W f - φ r * valR x W g := by
  have hc : valR x W (constFn p W r) = φ r := GlobalTheory.Points.valR_constFn_of_over p φ x hx W h r
  rw [← hc]
  unfold valR
  simp only [dif_pos h, map_sub, map_mul]

theorem isWt_sub_const_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (α : Q.X) (W : Y.H.left.Opens) (f g : Γ(Y.H.left, W)) (r : R), IsWt Y α W f → IsWt Y α W g → IsWt Y α W (f - constFn Y.H.hom W r * g) := by
  intro R _ _ Q Ω _ _ _ oa Y α W f g r hf hg S _ φ x x' c a a' ha ha' hW hW' hq hc
  have h1 := hf S φ x x' c a a' ha ha' hW hW' hq hc
  have h2 := hg S φ x x' c a a' ha ha' hW hW' hq hc
  have e : a ≫ Y.H.hom = spMap φ := by rw [ha]; exact Over.w x
  have e' : a' ≫ Y.H.hom = spMap φ := by rw [ha']; exact Over.w x'
  rw [valR_sub_const_mul _ φ a e W hW, valR_sub_const_mul _ φ a' e' W hW', h1, h2]
  ring

end GlobalTheory.HeatMod
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRaynaudTorusWeightFunction_sub_const_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (α : Q.X) (W : Y.H.left.Opens) (f g : Γ(Y.H.left, W)) (r : R), IsWt Y α W f → IsWt Y α W g → IsWt Y α W (f - constFn Y.H.hom W r * g) := by
  atlas_forward_decl GlobalTheory.HeatMod.isWt_sub_const_mul
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRaynaudFourierTerm_sub_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (k : ℕ) (α : Q.X) (σ σ' : Q.SecB k α) (τ τ' : SecM Y.q.left Q.P.L k) (e : R), IsTerm Y k α σ τ → IsTerm Y k α σ' τ' → IsTerm Y k α (σ' - constFn Q.P.A.hom ⊤ e • σ) (τ' - constFn Y.H.hom ⊤ e • τ) := by
  first | exact @GlobalTheory.HeatTermLin.isTerm_sub_smul | exact GlobalTheory.HeatTermLin.isTerm_sub_smul | (intros; apply GlobalTheory.HeatTermLin.isTerm_sub_smul <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaShiftFunctionalEq_sub_constFn_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (mu α : Q.X) (σ σ' : Q.SecB k α) (σ₁ σ₁' : Q.SecB k (α + k • mu)) (c e e₁ : R), ShiftEq Q k mu α σ σ₁ 0 σ₁ → ShiftEq Q k mu α (σ' - constFn Q.P.A.hom ⊤ e • σ) (σ₁' - constFn Q.P.A.hom ⊤ e₁ • σ₁) c σ₁ → ShiftEq Q k mu α σ' σ₁' (c + e₁ - e) σ₁ := by
  first | exact @GlobalTheory.HeatMod.shiftEq_of_sub_constFn_smul | exact GlobalTheory.HeatMod.shiftEq_of_sub_constFn_smul | (intros; apply GlobalTheory.HeatMod.shiftEq_of_sub_constFn_smul <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatMod

namespace GlobalTheory.HeatMod

theorem opMod {R : Type} [CommRing R] (G : Over (Sp R)) {n : ℕ} (dd : Fin n → Fld G.left)
    (Θ M : Matrix (Fin n) (Fin n) R) (u c₁ c₂ : Fin n → R) (d : Fld G.left) {W : G.left.Opens} (p p' : Γ(G.left, W))
    (k : ℕ) (O : G.left.Opens) (f : Γ(G.left, O)) :
    op G dd (Θ + M) (u - c₁) (fun O f => d O f - combF G.hom dd c₂ O f) p p' k O f =
      op G dd Θ u d p p' k O f - 2 * (k : Γ(G.left, O)) * combF G.hom dd c₂ O f - quadF G.hom dd M O f -
        2 * combF G.hom dd c₁ O f := by
  have hc : ∀ a b : R, constFn G.hom O (a + b) = constFn G.hom O a + constFn G.hom O b := fun a b => by
    simp [constFn]
  have hs : ∀ a b : R, constFn G.hom O (a - b) = constFn G.hom O a - constFn G.hom O b := fun a b => by
    simp [constFn]
  simp only [op, combF, quadF, Matrix.add_apply, Pi.sub_apply, hc, hs, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

theorem rsT_resG_constFn {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {U V : Z.Opens} (hV : V ≤ U)
    (x : R) : rsT (resG Z (le_top : U ≤ ⊤) (constFn s ⊤ x)) V = constFn s V x := by
  rw [← GlobalTheory.KS.rsT_of_le (le_top : U ≤ ⊤), GlobalTheory.KS.rsT_rsT le_top hV, GlobalTheory.KS.rsT_constFn _ le_top]

theorem defect_cancel {R X : Type} [CommRing R] [AddCommGroup X] (w : X → X →+ R) (π π' : X → R) (half : R)
    (h2 : 2 * half = 1) (hw1 : ∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) (hw2 : ∀ mu mu', w mu mu' = w mu' mu)
    (hπ' : ∀ mu mu', π' (mu + mu') = π' mu + π' mu') (hπ : ∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu)
    (k : ℕ) (mu α : X) :
    0 = 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu +
      (-(2 * (k : R) * (π (α + k • mu) - half * w (α + k • mu) (α + k • mu))) - w (α + k • mu) (α + k • mu) -
        2 * π' (α + k • mu)) -
      (-(2 * (k : R) * (π α - half * w α α)) - w α α - 2 * π' α) := by
  have wsm : ∀ (m : ℕ) (x y : X), w (m • x) y = (m : R) * w x y := by
    intro m x y
    induction m with
    | zero =>
      simp only [zero_smul, Nat.cast_zero, zero_mul]
      have := hw1 0 0 y
      simp only [add_zero] at this
      linear_combination -this
    | succ m ih => rw [succ_nsmul, hw1, ih]; push_cast; ring
  have psm : ∀ (m : ℕ) (x : X), π' (m • x) = (m : R) * π' x := by
    intro m x
    induction m with
    | zero =>
      simp only [zero_smul, Nat.cast_zero, zero_mul]
      have := hπ' 0 0
      simp only [add_zero] at this
      linear_combination -this
    | succ m ih => rw [succ_nsmul, hπ', ih]; push_cast; ring
  have qsm : ∀ (m : ℕ) (x : X), π (m • x) = (m : R) * π x + half * ((m : R) ^ 2 - m) * w x x := by
    intro m x
    induction m with
    | zero =>
      have := hπ 0 0
      simp only [add_zero, map_zero, AddMonoidHom.zero_apply] at this
      simp only [zero_smul, Nat.cast_zero]
      linear_combination -this
    | succ m ih =>
      rw [succ_nsmul, hπ, ih, map_nsmul, nsmul_eq_mul]
      push_cast
      linear_combination (-(m : R) * w x x) * h2
  simp only [hπ, hπ', hw1, map_add, wsm, map_nsmul, psm, qsm, nsmul_eq_mul, hw2 α mu]
  linear_combination (-((k : R) ^ 2 * w mu mu + 2 * (k : R) ^ 2 * w mu α)) * h2

theorem exists_heat_defect_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), IsBasic Y h → HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) → (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) → (∀ mu mu', w mu mu' = w mu' mu) → (∀ mu mu', π' (mu + mu') = π' mu + π' mu') → (∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu) → ∃ h' : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h' ∧ HasDefect Y h' (fun _ _ _ => 0) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv D h w π π' hB hD hw1 hw2 hπ' hπ
  let ℓ₁ : Dd.toPre.X →+ R := AddMonoidHom.mk' π' hπ'
  let half : R := algebraMap ℚ R (1 / 2)
  have h2 : (2 : R) * half = 1 := by
    simp only [half]
    rw [← map_ofNat (algebraMap ℚ R) 2, ← map_mul]
    norm_num
  let ℓ₂ : Dd.toPre.X →+ R := AddMonoidHom.mk' (fun x => π x - half * w x x) (fun a b => by
    simp only [hπ, hw1, map_add]
    rw [hw2 b a]
    linear_combination (-(w a b)) * h2)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_torus_invariantField_const_coeffs R Dd O oa Y n v dd hv ℓ₁
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.T.exists_torus_invariantField_const_coeffs R Dd O oa Y n v dd hv ℓ₂
  obtain ⟨M, hMs, hMa, hMg⟩ := GlobalTheory.T.exists_symmetric_second_order_operator_of_character_form R Dd O oa Y n v dd hv w hw1 hw2
  obtain ⟨⟨a1, a2, a3⟩, kc, wt₂, pb₂⟩ := hc₂
  let h' : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D :=
    { Θ := h.Θ + M
      symm := by rw [Matrix.transpose_add, h.symm, hMs]
      u := h.u - c₁
      J := h.J
      W := h.W
      j := h.j
      d := fun i O f => h.d i O f - combF Y.H.hom dd c₂ O f
      p := h.p
      p' := h.p'
      cover := h.cover
      le := h.le
      lift := fun i => by
        obtain ⟨⟨f1, f2, f3⟩, fc⟩ := h.lift i
        refine ⟨⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' hh hW f => ?_⟩, fun W hW r => ?_⟩
        · dsimp only; rw [f1 W hW, a1 W le_top]; ring
        · dsimp only; rw [f2 W hW, a2 W le_top]; ring
        · dsimp only; rw [f3 W W' hh hW, a3 W W' hh le_top, map_sub]
        · dsimp only; rw [fc W hW, kc, sub_zero]
      glue := fun k i i' O hO f => by
        have hle : O ≤ Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U (h.j i) ⊓ Dd.toPre.P.L.U (h.j i')) := fun x hx =>
          ⟨h.le i (hO hx).1, h.le i' (hO hx).2⟩
        rw [opMod, opMod, h.glue k i i' O hO f, pb₂ _ _ O k f hle, hMg _ _ O k f hle, hc₁.2.2.2 _ _ O k f hle]
        ring }

  have wsm : ∀ (m : ℕ) (x y : Dd.toPre.X), w (m • x) y = (m : R) * w x y := by
    intro m x y
    induction m with
    | zero => simp only [zero_smul, Nat.cast_zero, zero_mul]; have := hw1 0 0 y; simp only [add_zero] at this; linear_combination -this
    | succ m ih => rw [succ_nsmul, hw1, ih]; push_cast; ring
  let e : ℕ → Dd.toPre.X → R := fun k α => -(2 * (k : R) * ℓ₂ α) - w α α - 2 * ℓ₁ α
  have key : ∀ k α σ σ', TActs Y h' k α σ σ' →
      TActs Y h k α σ (σ' - constFn Dd.toPre.P.A.hom ⊤ (e k α) • σ) := by
    rintro k α σ σ' ⟨τ, τ', hτ, hτ', hA⟩
    refine ⟨τ, τ' - constFn Y.H.hom ⊤ (e k α) • τ, hτ, GlobalTheory.T.isRaynaudFourierTerm_sub_smul R Dd.toPre O oa Y k α σ σ' τ τ' (e k α) hτ hτ',
      fun i => ?_⟩
    have hA' := hA i
    obtain ⟨V, hV⟩ := (hB i).1
    have hwt := GlobalTheory.T.raynaudFourierTerm_chartRestriction_isWeight R Dd.toPre O oa Y k α σ τ hτ (h.j i) (h.W i) ⟨V, hV⟩ (h.le i)
    change rsT (τ'.f fun _ => h.j i) (h.W i) = op Y.H dd (h.Θ + M) (h.u - c₁)
      (fun O f => h.d i O f - combF Y.H.hom dd c₂ O f) (h.p i) (h.p' i) k (h.W i)
      (rsT (τ.f fun _ => h.j i) (h.W i)) at hA'
    rw [opMod, wt₂ α _ ⟨V, hV⟩ _ hwt, hMa α _ ⟨V, hV⟩ _ hwt, hc₁.2.2.1 α _ ⟨V, hV⟩ _ hwt] at hA'
    have hle' : h.W i ≤ LB.wchart Dd.toPre.P.L (K := Fin 1) (fun _ => Y.q.left) (fun _ => h.j i) := fun x hx =>
      Set.mem_iInter.2 fun _ => h.le i hx
    have hce : constFn Y.H.hom (h.W i) (e k α) = -(2 * (k : Γ(Y.H.left, h.W i)) * constFn Y.H.hom (h.W i) (ℓ₂ α)) -
        constFn Y.H.hom (h.W i) (w α α) - 2 * constFn Y.H.hom (h.W i) (ℓ₁ α) := by
      have hcf : ∀ a, constFn Y.H.hom (h.W i) a = ((Y.H.hom.appLE ⊤ (h.W i) (fun _ _ => trivial)).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) a := fun _ => rfl
      simp only [hcf, e, map_sub, map_neg, map_mul, map_natCast, map_ofNat]
    change rsT ((τ'.f fun _ => h.j i) - resG Y.H.left le_top (constFn Y.H.hom ⊤ (e k α)) * τ.f fun _ => h.j i) (h.W i) = _
    rw [GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_mul, rsT_resG_constFn, hA', hce]
    · ring
    · exact hle'
  refine ⟨h', fun i => ?_, ?_⟩
  · obtain ⟨b1, b2, b3, b4⟩ := hB i
    refine ⟨b1, b2, b3, fun α V hV f hf => ?_⟩
    show IsWt Y α _ (h.d i _ f - combF Y.H.hom dd c₂ _ f)
    rw [wt₂ α _ ⟨V, rfl⟩ f hf]
    exact GlobalTheory.T.isRaynaudTorusWeightFunction_sub_const_mul R Dd.toPre O oa Y α _ _ f (ℓ₂ α) (b4 α V hV f hf) hf
  · intro k mu α σ σ' σ₁ σ₁' hk hS hT1 hT2
    have H := hD k mu α σ _ σ₁ _ hk hS (key _ _ _ _ hT1) (key _ _ _ _ hT2)
    have H2 := GlobalTheory.T.thetaShiftFunctionalEq_sub_constFn_smul R Dd.toPre k mu α σ σ' σ₁ σ₁' _ _ _ hS H
    convert H2 using 1
    exact defect_cancel w π π' half h2 hw1 hw2 hπ' hπ k mu α

end GlobalTheory.HeatMod
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heatOperator_period_defect_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), IsBasic Y h → HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) → (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) → (∀ mu mu', w mu mu' = w mu' mu) → (∀ mu mu', π' (mu + mu') = π' mu + π' mu') → (∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu) → ∃ h' : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h' ∧ HasDefect Y h' (fun _ _ _ => 0) := by
  atlas_forward_decl GlobalTheory.HeatMod.exists_heat_defect_zero
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.heat_commuting_periods_exists : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∃ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h ∧ HasDefect Y h (fun _ _ _ => 0) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv m t gam hmon ht D hD
  obtain ⟨h, w, π, π', hb, hdef⟩ := GlobalTheory.T.exists_torusInvariant_heatOperator_polynomial_defect R Dd O oa Y n v dd hv m t gam hmon ht D hD
  have hcoc := GlobalTheory.T.heatOperator_period_defect_isCocycle R Dd O oa Y n v dd hv D h _ hb hdef
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.cocycle_polynomialDefect_bilinear_additive_parts R Dd.toPre.X w π π' hcoc
  exact GlobalTheory.T.exists_heatOperator_period_defect_zero R Dd O oa Y n v dd hv D h w π π' hb hdef h1 h2 h3 h4
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusInvariant_heatOperator_commuting_periods : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∃ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h ∧ HasDefect Y h (fun _ _ _ => 0) := by
  atlas_forward_decl GlobalTheory.heat_commuting_periods_exists
end
