import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataMatrixActionRingHomProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorActionCompatibleWithDegeneration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionProps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataLatticeFactorProps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationTauBalancedOfAdjointIntMatrice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinCombPullbackTransportIsoWithValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompLinCombGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeStepGeneratorTensorPowerPairsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaValueProductFormulaDegeneration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamPtsPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLambdaGeneratorZpowWithPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoGluedFromLinCombPullback

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordTensorData_matrixAction_ringHom_properties : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W), (∀ a, IsMonHom (T.act a)) ∧ T.act 1 = 𝟙 _ ∧ (∀ a b, T.act (a * b) = T.act b ≫ T.act a) ∧ ∀ a b, T.act (a + b) = padd D'.P.A (T.act a) (T.act b) := by
  first | exact @GlobalTheory.Mum.TensAct.act_ring | exact GlobalTheory.Mum.TensAct.act_ring | (intros; apply GlobalTheory.Mum.TensAct.act_ring <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_action_compatible_with_degeneration : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (s : SymUnit r), letI := T.mod s; ∀ (a : TensO s) (y : D'.X), D'.c (a • y) = D'.c y ≫ T.act (TensO.mat s a) := by
  first | exact @GlobalTheory.Mum.Tens.c_smul | exact GlobalTheory.Mum.Tens.c_smul | (intros; apply GlobalTheory.Mum.Tens.c_smul <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordTensorData_factorInclusion_projection_props : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (i₀ : Fin r), IsMonHom (T.inc i₀) ∧ T.inc i₀ ≫ T.pr i₀ = 𝟙 _ ∧ T.pr i₀ ≫ T.inc i₀ = T.act (Matrix.single i₀ i₀ 1) ∧ ∀ y, D'.c (T.xi i₀ y) = D.c y ≫ T.inc i₀ := by
  first | exact @GlobalTheory.Mum.tens_inc_pr_facts | exact GlobalTheory.Mum.tens_inc_pr_facts | (intros; apply GlobalTheory.Mum.tens_inc_pr_facts <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordTensorData_latticeFactor_props : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (s : SymUnit r) (i₀ : Fin r), letI := T.mod s; (∀ y, T.xp i₀ (T.xi i₀ y) = y) ∧ (∀ z, T.xi i₀ (T.xp i₀ z) = TensO.idem s i₀ • z) ∧ Function.Injective (fun y => star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y) ∧ ∀ z, ∃ y, star (TensO.idem s i₀) • z = star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y := by
  first | exact @GlobalTheory.Mum.tens_factor_latt | exact GlobalTheory.Mum.tens_factor_latt | (intros; apply GlobalTheory.Mum.tens_factor_latt <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiAdj_mumfordTensorPower_of_posDef : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W) (a : TensO (symUnitOf W h)), RosatiAdj D'.toPre.P.A D'.toPre.P.L (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) := by
  first | exact @GlobalTheory.Mum.rosatiAdj_tens | exact GlobalTheory.Mum.rosatiAdj_tens | (intros; apply GlobalTheory.Mum.rosatiAdj_tens <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TensBal

theorem transpose_mul_eq {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det)
    (a : TensO (symUnitOf W h)) :
    (TensO.mat _ a).transpose * (W + W.transpose) = (W + W.transpose) * TensO.mat _ (star a) := by
  have hb : ((symUnitOf W h).1 : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose := rfl
  rw [TensO.star_def]
  show _ = (W + W.transpose) * (((((symUnitOf W h).1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
    (TensO.mat _ a).transpose * ((symUnitOf W h).1 : Matrix (Fin r) (Fin r) ℤ)))
  rw [hb.symm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem tauBal_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W), letI := T.mod (symUnitOf W h); ∀ a : TensO (symUnitOf W h), D'.toPre.TauBal (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) (fun y => a • y) (fun y => star a • y) := by
  intro R _ _ _ _ D D' r W h _ T a
  exact GlobalTheory.T.tensorDegeneration_tauBalanced_of_adjointIntMatrices R _ D D' W T (TensO.mat _ a) (TensO.mat _ (star a)) (transpose_mul_eq W h a)

end GlobalTheory.Mum.TensBal
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorDegData_periods_balanced_matrixAction : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W), letI := T.mod (symUnitOf W h); ∀ a : TensO (symUnitOf W h), D'.toPre.TauBal (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) (fun y => a • y) (fun y => star a • y) := by
  atlas_forward_decl GlobalTheory.Mum.TensBal.tauBal_tens
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linCombPullbackTransportIso_with_values : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {K I : Type} [Fintype K] [Fintype I] (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (w : LB.Iso L' (LB.LinComb L ψ δ)), w.IsGen → L.IsLB → L'.IsLB → ∀ (σ : I → (Y ⟶ X')) (e : I → ℤ), ∃ v : LB.Iso (LB.LinComb L' σ e) (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2)), v.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' → gm q z _ (v.s (fun p => J (q ≫ σ p.1 ≫ ψ p.2), fun i => J' (q ≫ σ i))) = ∏ i, gm (q ≫ σ i) z _ (w.s (fun k => J (q ≫ σ i ≫ ψ k), J' (q ≫ σ i))) ^ e i := by
  first | exact @GlobalTheory.Mum.exists_transIso_linComb | exact GlobalTheory.Mum.exists_transIso_linComb | (intros; apply GlobalTheory.Mum.exists_transIso_linComb <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleIso_comp_linCombGenerator : ∀ {X Y : Scheme.{0}} {L : LB X} {A : LB Y} {K K₁ : Type} [Fintype K] [Fintype K₁] (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ), L.IsLB → A.IsLB → ∀ (u : LB.Iso A (LB.LinComb L φ₀ ε₀)), u.IsGen → ∀ (c : LB.Gen (LB.LinComb L (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)))), c.IsGen → ∃ u' : LB.Iso A (LB.LinComb L φ₁ ε₁), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (a : A.ι), q z ∈ A.U a → Good L z J → gm q z _ (u'.s (fun k => J (q ≫ φ₁ k), a)) = gm q z _ (u.s (fun k => J (q ≫ φ₀ k), a)) * val c q z J := by
  first | exact @GlobalTheory.LinCombComp.exists_iso_comp_val | exact GlobalTheory.LinCombComp.exists_iso_comp_val | (intros; apply GlobalTheory.LinCombComp.exists_iso_comp_val <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_value_product_formula_degeneration : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = (∏ K : ULift.{0} (Finset (Fin 2)), gm ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left) z _ (T.w.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left ≫ tensφ T.pr k), J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left))) ^ ((-1 : ℤ) ^ (2 - K.down.card))) * (∏ i, ∏ j, (cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) * (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j)) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i)) ^ (-W i j)) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  first | exact @GlobalTheory.Mum.Tens.tau_periods | exact GlobalTheory.Mum.Tens.tau_periods | (intros; apply GlobalTheory.Mum.Tens.tau_periods <;> assumption)
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem tens_lam_core : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W), ∃ w₁ : LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) (LB.LinComb D.toPre.P.L (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2) (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)), w₁.IsGen ∧ ∀ (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = gm (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z _ (w₁.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2), fun I => J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  intro R _ _ I D D' r W T
  obtain ⟨v, hv, hvv⟩ := GlobalTheory.T.exists_linCombPullbackTransportIso_with_values (L := D.toPre.P.L) (L' := D'.toPre.P.L) (tensφ T.pr) (tensε W) T.w T.w_gen
    D.toPre.P.isLB D'.toPre.P.isLB
    (fun K : ULift.{0} (Finset (Fin 2)) => (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left)
    (fun K => (-1 : ℤ) ^ (2 - K.down.card))
  obtain ⟨c, hc, hcv⟩ := GlobalTheory.T.exists_cubeStep_generator_tensorPowerPairs (⟨D.toPre.P.L, D.toPre.rig, D.toPre.P.isLB, D.toPre.rig_gen⟩ : RigLB D.toPre.P.A)
    D.toPre.cub W T.pr T.pr_hom
  obtain ⟨u, hu, huv⟩ := GlobalTheory.T.exists_lineBundleIso_comp_linCombGenerator (A := abelian₂ D'.toPre.P.A D'.toPre.P.L) _ _
    (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1)
      (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2)
    (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) D.toPre.P.isLB (LB.isLB_linComb D'.toPre.P.isLB _ _) v hv c hc
  refine ⟨u, hu, fun a b z J J' hJ hJ' => ?_⟩
  have e1 := hvv _ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z J J' hJ hJ'
  have e2 := hcv (TK R) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)) z J hJ
  rw [huv _ _ z J _ (hJ'.mem _ _) hJ, e2]
  refine (GlobalTheory.T.theta_value_product_formula_degeneration R I D D' W T a b z J J' hJ hJ').trans ?_
  exact congrArg (· * _) (congrArg (· * _) e1.symm)

end GlobalTheory.Mum
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorData_biextension_periods : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W), ∃ w₁ : LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) (LB.LinComb D.toPre.P.L (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2) (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)), w₁.IsGen ∧ ∀ (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = gm (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z _ (w₁.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2), fun I => J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  atlas_forward_decl GlobalTheory.Mum.tens_lam_core
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_glued_from_linComb_pullback : ∀ {X X' Y : Scheme.{0}} {M : LB Y}, M.IsLB → ∀ {L' : LB X'}, L'.IsLB →
    ∀ {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (X' ⟶ Y)) (ε : K → ℤ) (ψ : K' → (X ⟶ Y)) (e : K' → ℤ)
    (F : X ⟶ X') (w₁ : LB.Iso L' (LB.LinComb M φ ε)), w₁.IsGen →
    ∀ (u : LB.Gen (LB.LinComb M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim ε (fun i => - e i)))), u.IsGen →
    ∃ w : LB.Iso (LB.LinComb M ψ e) (L'.pull F), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (J : (Z ⟶ Y) → M.ι), Good M z J → ∀ j' : L'.ι, F (f z) ∈ L'.U j' →
        gw w f z j' (fun i => J (f ≫ ψ i)) = (gv w₁ (f ≫ F) z (fun k => J ((f ≫ F) ≫ φ k)) j')⁻¹ * val u f z J := by
  first | exact @GlobalTheory.Mum.iso_linComb_pull_glue | exact GlobalTheory.Mum.iso_linComb_pull_glue | (intros; apply GlobalTheory.Mum.iso_linComb_pull_glue <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LamComb

section Generators

variable {X Y Z : Scheme.{0}} {L : LB X} {J K : Type} [Fintype J] [Fintype K]

omit [Fintype J] in
theorem wchart_le (φ : J → K → (Y ⟶ X)) [Fintype J] (jj : J × K → L.ι) (i : J) :
    LB.wchart L (fun q : J × K => φ q.1 q.2) jj ≤ LB.wchart L (φ i) (fun k => jj (i, k)) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)

def prodGen (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ) (δ : J → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) :
    LB.Gen (LB.LinComb L (fun q : J × K => φ q.1 q.2) (fun q => δ q.1 * ε q.1 q.2)) where
  s := fun jj => ∏ i, res (wchart_le φ jj i) ((t i).s (fun k => jj (i, k))) ^ δ i

theorem gm_prodGen (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ) (δ : J → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i)))
    (r : Z ⟶ Y) (z : Z) (jj : J × K → L.ι) (h : r z ∈ LB.wchart L (fun q : J × K => φ q.1 q.2) jj) :
    gm r z (LB.wchart L (fun q : J × K => φ q.1 q.2) jj) ((prodGen φ ε δ t).s jj) =
      ∏ i, gm r z (LB.wchart L (φ i) (fun k => jj (i, k))) ((t i).s (fun k => jj (i, k))) ^ δ i :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    (map_zpow _ _ _).trans (congrArg (· ^ δ i) (gm_res r z _ h _)))

theorem isGen_prodGen (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ) (δ : J → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i)))
    (ht : ∀ i, (t i).IsGen) : (prodGen φ ε δ t).IsGen := by
  intro jj jj'
  refine unit_ext fun y hy => ?_
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun q : J × K => φ q.1 q.2) jj ⊓
    LB.wchart L (fun q : J × K => φ q.1 q.2) jj' := hy
  refine (gm_res (𝟙 Y) y _ hm _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y jj jj' hm.1 hm.2) (gm_res (𝟙 Y) y _ hm _))).symm)
  refine (gm_prodGen φ ε δ t (𝟙 Y) y jj hm.1).trans
    (Eq.trans ?_ (congrArg _ (gm_prodGen φ ε δ t (𝟙 Y) y jj' hm.2)).symm)
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gen_trans (ht i) (𝟙 Y) y (wchart_le φ jj i hm.1) (wchart_le φ jj' i hm.2), mul_zpow]
  congr 1
  rw [trF, ← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_mul, mul_comm]

theorem val_prodGen (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ) (δ : J → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i)))
    (r : Z ⟶ Y) {z : Z} {I : (Z ⟶ X) → L.ι} (hI : Good L z I) :
    val (prodGen φ ε δ t) r z I = ∏ i, val (t i) r z I ^ δ i :=
  gm_prodGen φ ε δ t r z _ (hI.mem _ r)

end Generators

theorem prod_zpow_sum {U J : Type} [CommGroup U] (s : Finset J) (a : U) (f : J → ℤ) :
    ∏ j ∈ s, a ^ f j = a ^ ∑ j ∈ s, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

theorem exists_gen_lam_comb : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ {r : ℕ}
    (e c : Fin r → ℤ), ∑ j, e j * c j = 1 →
    ∃ u : LB.Gen (LB.LinComb D.P.L
        (Sum.elim (fun q : Fin r × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ c q.1) q.2)
          (fun I : ULift (Finset (Fin 2)) => (psum D.P.A (x2 D.P.A) I.down).left))
        (Sum.elim (fun q => e q.1 * Oε q.2) (fun I => -((-1) ^ (2 - I.down.card))))), u.IsGen ∧
      ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val (D.tau a b) (𝟙 _) z J = val u (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J *
          ∏ j, val (D.tau a (c j • b)) (𝟙 _) z J ^ e j := by
  intro R _ _ D hD r e c hec
  choose g hg hv using fun j => GlobalTheory.T.exists_lambdaGenerator_zpow_with_periods D hD (c j)
  have hF : FormEq (fun q : Fin r × (Fin 4 ⊕ Fin 4) => Sum.elim
        (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ c q.1))
        (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A)) q.2)
      (fun q => e q.1 * Sum.elim Oε (fun l => -c q.1 * Oε l) q.2)
      (Sum.elim (fun q : Fin r × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ c q.1) q.2)
          (fun I : ULift (Finset (Fin 2)) => (psum D.P.A (x2 D.P.A) I.down).left))
      (Sum.elim (fun q => e q.1 * Oε q.2) (fun I => -((-1) ^ (2 - I.down.card)))) := by
    intro U _ h
    simp only [Fintype.prod_prod_type, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_comm]
    have k : ∀ l, ∏ j, h (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A) l) ^ (e j * (-c j * Oε l)) =
        h (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A) l) ^ (-Oε l) := fun l => by
      rw [prod_zpow_sum]
      congr 1
      calc ∑ j, e j * (-c j * Oε l) = (∑ j, e j * c j) * (-Oε l) := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = -Oε l := by rw [hec, _root_.one_mul]
    simp only [k]
    rw [← Equiv.ulift.symm.prod_comp, show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} from by decide,
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
      Fin.prod_univ_four]
    have q0 : psum D.P.A (x2 D.P.A) ∅ = 1 := rfl
    have q1 : psum D.P.A (x2 D.P.A) {0} = fst D.P.A D.P.A := _root_.mul_one _
    have q2 : psum D.P.A (x2 D.P.A) {1} = snd D.P.A D.P.A := _root_.mul_one _
    have q3 : psum D.P.A (x2 D.P.A) {0, 1} = fst D.P.A D.P.A * snd D.P.A D.P.A :=
      congrArg (fst D.P.A D.P.A * ·) (_root_.mul_one _)
    simp [q0, q1, q2, q3, GlobalTheory.PolDeg.lamPts, Oε]
    generalize h (fst D.P.A D.P.A * snd D.P.A D.P.A).left = A, h (fst D.P.A D.P.A).left = A₁,
      h (snd D.P.A D.P.A).left = A₂, h (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left = A₀
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨u, hu, hval⟩ := exists_gen D.P.isLB hF (prodGen _ _ e g) (isGen_prodGen _ _ e g hg)
  refine ⟨u, hu, fun a b z J hJ => ?_⟩
  rw [hval _ _ z J hJ, val_prodGen _ _ e g _ hJ, ← Finset.prod_mul_distrib]
  have : ∀ j, val (g j) (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J ^ e j *
      val (D.tau a (c j • b)) (𝟙 _) z J ^ e j = val (D.tau a b) (𝟙 _) z J ^ (e j * c j) := fun j => by
    rw [← mul_zpow, mul_comm, hv j a b z J hJ, ← zpow_mul, mul_comm]
  rw [Finset.prod_congr rfl fun j _ => this j, prod_zpow_sum, hec, zpow_one]

end GlobalTheory.Mum.LamComb
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_biextension_generator_bezout_combination : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ {r : ℕ}
    (e c : Fin r → ℤ), ∑ j, e j * c j = 1 →
    ∃ u : LB.Gen (LB.LinComb D.P.L
        (Sum.elim (fun q : Fin r × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ c q.1) q.2)
          (fun I : ULift (Finset (Fin 2)) => (psum D.P.A (x2 D.P.A) I.down).left))
        (Sum.elim (fun q => e q.1 * Oε q.2) (fun I => -((-1) ^ (2 - I.down.card))))), u.IsGen ∧
      ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val (D.tau a b) (𝟙 _) z J = val u (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J *
          ∏ j, val (D.tau a (c j • b)) (𝟙 _) z J ^ e j := by
  atlas_forward_decl GlobalTheory.Mum.LamComb.exists_gen_lam_comb
end

section
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensPair

theorem pair_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W), (∃ w₁ : LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) (LB.LinComb D.toPre.P.L (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2) (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)), w₁.IsGen ∧ ∀ (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = gm (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z _ (w₁.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2), fun I => J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j)) → ∀ (i₀ : Fin r), letI := T.mod (symUnitOf W h); ∃ w : LB.Iso (abelian₂ D.toPre.P.A D.toPre.P.L) ((abelian₂ D'.toPre.P.A D'.toPre.P.L).pull (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D'.toPre.P.L z J → Good D.toPre.P.L z J' → val (D.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b)).left z J J' * val (D'.toPre.tau (T.xi i₀ a) (TensO.binv (symUnitOf W h) • T.xi i₀ b)) (𝟙 _) z J := by
  intro R _ _ _ _ D D' r W h _ T hw i₀
  obtain ⟨w₁, hw₁, hv₁⟩ := hw
  have hsum : ∑ j, (W + W.transpose) i₀ j * TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ = 1 := by
    have hb : (((symUnitOf W h).1 : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose :=
      IsUnit.unit_spec _
    have key := congrFun (congrFun (Units.mul_inv (symUnitOf W h).1) i₀) i₀
    rw [hb, Matrix.mul_apply, Matrix.one_apply_eq] at key
    exact key
  obtain ⟨u₀, hu₀, hv₀⟩ := GlobalTheory.T.exists_biextension_generator_bezout_combination D.toPre D.tau_bimult (fun j => (W + W.transpose) i₀ j)
    (fun j => TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀) hsum
  obtain ⟨u, hu, hvu⟩ := exists_gen D.toPre.P.isLB
    (φ' := Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2) (fun I : ULift (Finset (Fin 2)) => (psum D.toPre.P.A (x2 D.toPre.P.A) I.down).left))
    (ε' := Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) (fun I : ULift (Finset (Fin 2)) => -((-1) ^ (2 - I.down.card))))
    (fun U _ hh => by
      clear hv₀ hv₁ hu₀ u₀ hw₁ w₁
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      refine congrArg (· * _) ?_
      simp only [Sum.elim_inl, GlobalTheory.TensPair.lamPts_pull, Fintype.prod_prod_type]
      symm
      rw [Finset.prod_eq_single i₀ ?_ (by simp)]
      · exact Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun l _ => by rw [if_pos rfl]
      · intro i _ hi
        refine Finset.prod_eq_one fun j _ => ?_
        rw [Fin.prod_univ_four, if_neg hi]
        simp only [GlobalTheory.PolDeg.lamPts, Oε, _root_.one_mul]
        simp [zpow_mul, zpow_neg]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_one]
        module)
    u₀ hu₀
  obtain ⟨w, hw, hvw⟩ := GlobalTheory.T.exists_iso_glued_from_linComb_pullback D.toPre.P.isLB (LB.isLB_linComb D'.toPre.P.isLB _ _) _ _ _ _ _ w₁ hw₁ u hu
  refine ⟨w, hw, fun a b z J J' hJ hJ' => ?_⟩

  suffices key : ∀ b' : D'.toPre.X, (∀ j, T.xe b' j = TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ • b) →
      val (D.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z J J' *
        val (D'.toPre.tau (T.xi i₀ a) b') (𝟙 _) z J by
    exact key _ (fun j => (Tens.xe_smul T (symUnitOf W h) (TensO.binv _) (T.xi i₀ b) j).trans (by
      rw [Finset.sum_eq_single i₀ (fun k _ hk => by rw [GlobalTheory.TensPair.xe_xi, if_neg hk, smul_zero]) (by simp),
        GlobalTheory.TensPair.xe_xi, if_pos rfl]))
  intro b' hb'
  have hPl : (lift (toUnit (TK R) ≫ D'.toPre.c (T.xi i₀ a)) (toUnit (TK R) ≫ D'.toPre.c b') : TK R ⟶ G2 D'.toPre.P.A).left =
      (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫
        (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left := by
    rw [GlobalTheory.TensPair.pt_pull T i₀ _ a b _ b' (GlobalTheory.TensPair.xe_xi T i₀ · a) hb']; rfl
  have t0 : ∀ x, val (D.toPre.tau 0 x) (𝟙 _) z J' = 1 := fun x => by
    have e := GlobalTheory.TauTwist.val_tau_nsmul (𝟙 (TK R)) hJ' D.tau_bimult 0 x x
    rw [zero_smul] at e
    simpa [cubN] using e
  have hPi : ∏ i, ∏ j, val (D.toPre.tau (T.xe (T.xi i₀ a) i) (T.xe b' j)) (𝟙 _) z J' ^ ((W + W.transpose) i j) =
      ∏ j, val (D.toPre.tau a (TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ • b)) (𝟙 _) z J' ^ ((W + W.transpose) i₀ j) := by
    rw [Finset.prod_eq_single i₀ (fun i _ hi => Finset.prod_eq_one fun j _ => by
      rw [GlobalTheory.TensPair.xe_xi, if_neg hi, t0, one_zpow]) (by simp)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [GlobalTheory.TensPair.xe_xi, if_pos rfl, hb']
  have e1 := hv₁ (T.xi i₀ a) b' z J' J hJ' hJ
  rw [hPi, hPl] at e1
  have e2 := hvw _ (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z J' hJ'
    (fun I => J (((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫
        (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left) ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))
    (hJ.mem _ _)
  have e3 := hv₀ a b z J' hJ'
  have e4 := hvu _ (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z J' hJ'
  clear hv₀ hvu hvw hv₁ hPi
  change val _ _ z J = gv w₁ _ z _ _ * _ at e1
  have hj : (fun I : ULift (Finset (Fin 2)) => J ((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫ (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left)) =
      (fun I => J (((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫ (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left) ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left)) :=
    funext fun I => by rw [Category.assoc]
  have e5 : GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z J J' = gw w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z (fun I : ULift (Finset (Fin 2)) => J ((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫ (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))
      (fun I => J' ((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫ (psum D.toPre.P.A (x2 D.toPre.P.A) I.down).left)) := rfl
  rw [e5, hj, e2, e1, e3, e4]
  have key : ∀ {G : Type} [CommGroup G] (A P X : G), A * P = X⁻¹ * A * (X * P) := fun A P X => by
    rw [_root_.mul_comm X⁻¹ A, _root_.mul_assoc, inv_mul_cancel_left]
  exact key (G := ((TK R).left.presheaf.stalk z)ˣ) _ _ _

end GlobalTheory.TensPair
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_data_factor_pairing_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W), (∃ w₁ : LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) (LB.LinComb D.toPre.P.L (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2) (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)), w₁.IsGen ∧ ∀ (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = gm (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z _ (w₁.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2), fun I => J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j)) → ∀ (i₀ : Fin r), letI := T.mod (symUnitOf W h); ∃ w : LB.Iso (abelian₂ D.toPre.P.A D.toPre.P.L) ((abelian₂ D'.toPre.P.A D'.toPre.P.L).pull (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D'.toPre.P.L z J → Good D.toPre.P.L z J' → val (D.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b)).left z J J' * val (D'.toPre.tau (T.xi i₀ a) (TensO.binv (symUnitOf W h) • T.xi i₀ b)) (𝟙 _) z J := by
  atlas_forward_decl GlobalTheory.TensPair.pair_pull
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem pairing_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W) (i₀ : Fin r), letI := T.mod (symUnitOf W h); ∃ w : LB.Iso (abelian₂ D.toPre.P.A D.toPre.P.L) ((abelian₂ D'.toPre.P.A D'.toPre.P.L).pull (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D'.toPre.P.L z J → Good D.toPre.P.L z J' → val (D.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b)).left z J J' * val (D'.toPre.tau (T.xi i₀ a) (TensO.binv (symUnitOf W h) • T.xi i₀ b)) (𝟙 _) z J := by
  intro R _ _ _ hA D D' r W h hP T i₀
  exact GlobalTheory.T.tensor_data_factor_pairing_pullback R hA D D' W h hP T (GlobalTheory.T.exists_tensorData_biextension_periods R _ D D' W T) i₀

end GlobalTheory.Mum
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordTensorPairing_factorInclusion_periods : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W) (i₀ : Fin r), letI := T.mod (symUnitOf W h); ∃ w : LB.Iso (abelian₂ D.toPre.P.A D.toPre.P.L) ((abelian₂ D'.toPre.P.A D'.toPre.P.L).pull (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D'.toPre.P.L z J → Good D.toPre.P.L z J' → val (D.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b)).left z J J' * val (D'.toPre.tau (T.xi i₀ a) (TensO.binv (symUnitOf W h) • T.xi i₀ b)) (𝟙 _) z J := by
  atlas_forward_decl GlobalTheory.Mum.pairing_factor
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem TensO.idem_binv_alg {r : ℕ} (s : SymUnit r) (i₀ : Fin r)
    (hp : 0 < (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀) :
    (∃ b : ℕ, 0 < b ∧ Star.star (TensO.idem s i₀) * TensO.idem s i₀ =
        b • (Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀)) ∧
      Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀ =
        Star.star (TensO.idem s i₀) * Star.star (TensO.binv s) * TensO.idem s i₀ ∧
      ∃ g : TensO s, g * (Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀) = TensO.idem s i₀ := by
  have hf : Star.star (TensO.binv s) = TensO.binv s := by
    show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ) = ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ)
    rw [TensO.inv_transpose, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hEE : (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ 1 =
      Matrix.single i₀ i₀ 1 := by simp
  have hET : (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ).transpose = Matrix.single i₀ i₀ 1 := by simp
  have hmain : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
      (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ).transpose * (s.1 : Matrix (Fin r) (Fin r) ℤ) *
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ) =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ) := by
    rw [hET, Matrix.mul_assoc _ (s.1 : Matrix (Fin r) (Fin r) ℤ), Units.mul_inv, Matrix.mul_one, Matrix.mul_assoc, hEE]
  have hefe : Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀ = TensO.binv s * TensO.idem s i₀ := hmain
  refine ⟨⟨((s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀).toNat, by omega, ?_⟩, by rw [hf], TensO.ofMat s s.1, ?_⟩
  · rw [hefe]
    have h : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
        (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ).transpose * (s.1 : Matrix (Fin r) (Fin r) ℤ) *
        Matrix.single i₀ i₀ (1 : ℤ) = ((s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀).toNat •
        (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ)) := by
      rw [hET, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.single i₀ i₀ (1 : ℤ)),
        Matrix.single_mul_mul_single, ← Matrix.mul_smul]
      congr 1
      rw [Matrix.smul_single, nsmul_eq_mul, Int.toNat_of_nonneg hp.le]
      simp
    exact h
  · rw [hefe]
    have h : (s.1 : Matrix (Fin r) (Fin r) ℤ) *
        (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ)) =
        Matrix.single i₀ i₀ (1 : ℤ) := by
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    exact h

theorem Tens.nonempty_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ),
      ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det →
      ∀ T : Tens D.toPre D'.toPre W, 1 ≤ r → (∃ F : Factor D.toPre D'.toPre, F.Alg) := by
  intro R _ _ _ hR D D' r W hpos hdet T hr
  let s := symUnitOf W hdet
  let i₀ : Fin r := ⟨0, hr⟩
  letI := T.mod s
  obtain ⟨hhom, h1, hmul, hadd⟩ := GlobalTheory.T.mumfordTensorData_matrixAction_ringHom_properties R D.toPre D'.toPre W T
  obtain ⟨hinc, hip, hpi, hcx⟩ := GlobalTheory.T.mumfordTensorData_factorInclusion_projection_props R D.toPre D'.toPre W T i₀
  obtain ⟨hxx, hxe, hinj, honto⟩ := GlobalTheory.T.mumfordTensorData_latticeFactor_props R D.toPre D'.toPre W T s i₀
  obtain ⟨w, hw, htau⟩ := GlobalTheory.T.mumfordTensorPairing_factorInclusion_periods R hR D D' W hdet hpos T i₀
  have hp : 0 < (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀ := by
    have h := hpos.diag_pos (i := i₀)
    have h' : (0 : ℝ) < (((W + W.transpose) i₀ i₀ : ℤ) : ℝ) := h
    exact_mod_cast h'
  exact ⟨{
    O := TensO s
    mod := T.mod s
    o := { onB := { act := fun a => T.act (TensO.mat s a)
                    hom := fun a => hhom _
                    map_one := h1
                    map_mul := fun a b => hmul _ _
                    map_add := fun a b => hadd _ _
                    rosati := GlobalTheory.T.rosatiAdj_mumfordTensorPower_of_posDef R hR D D' W hdet hpos T }
           c_lin := GlobalTheory.T.tensor_action_compatible_with_degeneration R D.toPre D'.toPre W T s
           tau_bal := GlobalTheory.T.tensorDegData_periods_balanced_matrixAction R hR D D' W hdet hpos T }
    e := TensO.idem s i₀
    f := TensO.binv s
    inc := T.inc i₀
    pr := T.pr i₀
    xi := T.xi i₀
    xp := T.xp i₀
    w := w
    idem := TensO.idem_mul_idem s i₀
    inc_hom := hinc
    pr_hom := T.pr_hom i₀
    inc_pr := hip
    pr_inc := hpi
    xp_xi := hxx
    xi_xp := hxe
    c_xi := hcx
    inj := hinj
    onto := honto
    w_gen := hw
    tau := htau }, TensO.idem_binv_alg s i₀ hp⟩

end GlobalTheory.Mum
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraic_factor_of_unimodular_tensor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, 1 ≤ r → (∃ F : Factor D.toPre D'.toPre, F.Alg) := by
  atlas_forward_decl GlobalTheory.Mum.Tens.nonempty_factor
end
