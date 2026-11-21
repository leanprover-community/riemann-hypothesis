import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
import Mathlib
import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentTypeLevelCharacterFiniteOrderRootsOfUni
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimitiveRootsCoeffFieldTrueColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardColumnComparisonsTrueColumnsStatement

section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentTypeLevel_character_finiteOrder_rootsOfUnity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (gp : Fin 2 → ℕ) (G : GLoc F E σ gp) (a t skip fc : ℕ) (zl : Bool) (_ : GLev S G a t 0 skip fc zl) (K : Type) [Field K] (s : K →+* ℂ), (∀ i, (gp i).Prime) → (∀ i, ∃ ζ : K, IsPrimitiveRoot ζ (gp i)) → ∃ N : ℕ, 0 < N ∧ ∀ x : S.U, ((S.chi x : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((S.chi x : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.unipotent_type_character_finite_order | exact GlobalTheory.unipotent_type_character_finite_order | (intros; apply GlobalTheory.unipotent_type_character_finite_order <;> assumption)
end

section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem formsTiedSym_chi_zero_finite : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), (∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)) → ∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U, (((Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ) :=
  fun D _ _ _ Tf h =>
    GlobalTheory.T.unipotentTypeLevel_character_finiteOrder_rootsOfUnity _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Tf.glev0 D.what₂.LL D.what₂.embLL D.host.g_prime (fun i => (h i).1)

end GlobalTheory
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitiveRoots_coeffField_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : Fin 2), (∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i)) ∧ ∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i - 1) := by
  first | exact @GlobalTheory.trueCols_exists_primitiveRoots | exact GlobalTheory.trueCols_exists_primitiveRoots | (intros; apply GlobalTheory.trueCols_exists_primitiveRoots <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem colsTiedSym_chiFin0 : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∃ C : ColsTiedSym (I.rec7 l Z), ∀ u, Formalism.MainNotions.RT.ChiFin0 (C.forms u) := by
  intro B X I hI hP l Z
  obtain ⟨C, -, -⟩ := GlobalTheory.T.exists_standardColumnComparisons_trueColumns I hI hP l Z
  refine ⟨C, fun u => ?_⟩
  exact GlobalTheory.formsTiedSym_chi_zero_finite (I.rec7 l Z) u _ _ (C.forms u)
    (fun i => GlobalTheory.T.exists_primitiveRoots_coeffField_trueColumns I hI l Z i)

end GlobalTheory.Mem.Col2.TC
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetricColumnForms_stepZeroFiniteCharacter : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∃ C : ColsTiedSym (I.rec7 l Z), ∀ u, Formalism.MainNotions.RT.ChiFin0 (C.forms u) := by
  atlas_forward_decl GlobalTheory.Mem.Col2.TC.colsTiedSym_chiFin0
end
