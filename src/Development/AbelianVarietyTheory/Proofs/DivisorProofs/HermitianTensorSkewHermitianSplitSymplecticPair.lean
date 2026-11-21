import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat

section
namespace GlobalTheory.ProjectionInclusion

theorem proj_incl : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E] {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (e : E), (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) : E → TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) E) e) = (τ : E → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) e := by
  intro F E _ _ _ _ _ v τ e
  refine Eq.trans ?_ (one_mul (τ e))
  rfl

end GlobalTheory.ProjectionInclusion
end

section
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.FourSumComposition

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_cA (σ : E →ₐ[F] E) {v : Pl F} (τ : E →ₐ[F] Fv F v) (z : AE F E) :
    piW τ (cA σ z) = piW (τ.comp σ) z := by

  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [piW, cA, GlobalTheory.AdelicU.compFin, GlobalTheory.AdelicU.splitProj_tmul]
  | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]

theorem piW_incM {v : Pl F} (τ : E →ₐ[F] Fv F v) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (i j : Fin m) :
    piW τ (incM F J i j) = τ (J i j) := by
  simp [incM, inclR, piW, GlobalTheory.AdelicU.compFin, GlobalTheory.AdelicU.splitProj_tmul]

theorem comp_comp {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl F} (τ : E →ₐ[F] Fv F v) : (τ.comp σ).comp σ = τ := by
  ext x
  simp [GlobalTheory.AdelicU.cm_conj_conj h x]

theorem sum_four {R : Type} [CommRing R] {m n : ℕ} (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R)
    (X U : Matrix (Fin m) (Fin n) R) :
    ∑ i, ∑ j, ∑ k, ∑ l, X i j * A k i * -B l j * U k l = ∑ k, ∑ l, (-(A * X * B.transpose)) k l * U k l := by

  have hR : ∀ k l, (-(A * X * B.transpose)) k l * U k l = ∑ j, ∑ i, X i j * A k i * -B l j * U k l := by
    intro k l
    simp only [Matrix.neg_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, neg_mul,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [hR]
  calc ∑ i, ∑ j, ∑ k, ∑ l, X i j * A k i * -B l j * U k l
      = ∑ i, ∑ k, ∑ j, ∑ l, X i j * A k i * -B l j * U k l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, ∑ l, X i j * A k i * -B l j * U k l := Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, X i j * A k i * -B l j * U k l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ i, ∑ j, X i j * A k i * -B l j * U k l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ j, ∑ i, X i j * A k i * -B l j * U k l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E), (∀ (i j : Fin m), (σ : E → E) (JA j i) = JA i j) → (∀ (i j : Fin n), (σ : E → E) (JB j i) = -JB i j) → ∀ (x u : Matrix (Fin m) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), Matrix.map x (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) = (0 : Matrix (Fin m) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) → Matrix.map u (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (AlgHom.comp τ σ)) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) = (0 : Matrix (Fin m) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) → (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) + (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (AlgHom.comp τ σ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) = ∑ k : Fin m, ∑ l : Fin n, (-(Matrix.map JA (⇑τ : E → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) * Matrix.map x (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (AlgHom.comp τ σ)) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) * Matrix.transpose (Matrix.map JB (⇑τ : E → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)))) k l * Matrix.map u (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) k l := by
  intro F E _ _ _ _ _ σ hσ v τ m n JA JB hA hB x u hx hu
  have hx' : ∀ i j, piW τ (x i j) = 0 := fun i j => by simpa using congrFun (congrFun hx i) j
  have hu' : ∀ k l, piW (τ.comp σ) (u k l) = 0 := fun k l => by simpa using congrFun (congrFun hu k) l

  have h1 : piW τ (GlobalTheory.WeilM.hTens (cA σ) (incM F JA) (incM F JB) x u) = 0 := by
    simp [GlobalTheory.WeilM.hTens, piW_cA, hu']

  have h2 : piW (τ.comp σ) (GlobalTheory.WeilM.hTens (cA σ) (incM F JA) (incM F JB) x u) =
      ∑ i, ∑ j, ∑ k, ∑ l, (x.map (piW (τ.comp σ))) i j * (JA.map τ) k i * -(JB.map τ) l j *
        (u.map (piW τ)) k l := by
    simp only [GlobalTheory.WeilM.hTens, map_sum, map_mul, piW_cA, comp_comp hσ, piW_incM, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hA k i, hB l j, map_neg]
  rw [h1, zero_add, h2]
  exact sum_four _ _ _ _

end GlobalTheory.FourSumComposition
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.HTensSplitPair

theorem piW_cA_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ w) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem piW_inclR_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (e : E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (inclR (F := F) (AF F) e) = τ e := by
  first
  | exact @_root_.GlobalTheory.ProjectionInclusion.proj_incl
  | exact _root_.GlobalTheory.ProjectionInclusion.proj_incl
  | (apply _root_.GlobalTheory.ProjectionInclusion.proj_incl <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProjectionInclusion.proj_incl <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProjectionInclusion.proj_incl <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProjectionInclusion.proj_incl ..)

theorem hTens_split_pair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E), (∀ i j, σ (JA j i) = JA i j) → (∀ i j, σ (JB j i) = -JB i j) → ∀ (x u : Matrix (Fin m) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) = 0 → u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) = 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) = ∑ k, ∑ l, (-(JA.map τ * x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) * (JB.map τ)ᵀ)) k l * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) k l := by
  first
  | exact @_root_.GlobalTheory.FourSumComposition.main
  | exact _root_.GlobalTheory.FourSumComposition.main
  | (apply _root_.GlobalTheory.FourSumComposition.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FourSumComposition.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FourSumComposition.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FourSumComposition.main ..)

end GlobalTheory.HTensSplitPair
end
end
