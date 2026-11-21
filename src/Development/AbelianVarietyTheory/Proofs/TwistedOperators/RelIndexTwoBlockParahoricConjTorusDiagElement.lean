import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMulMatrixVolumeOpenSubgroupIntegralGLStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockVolumeProdStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixEntrywiseProductMeasureUniformizerPowerBoxStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexConjParahoric
import BuildAid.ForwardExisting

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section
namespace GlobalTheory.ParIdx

theorem relIndex_parahoric_conj_mtor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ),
    (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom).relIndex (parahoric k A D) : ℝ) =
      (resCard k : ℝ) ^ ((Fintype.card A : ℤ) * sumAbs e) *
        (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom).relIndex (KO k D) : ℝ) := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.ParahoricConjugateOpen.relIndex_conj_parahoric
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.ParahoricConjugateOpen.relIndex_conj_parahoric
  | exact @_root_.GlobalTheory.ParahoricConjugateOpen.relIndex_conj_parahoric
  | exact _root_.GlobalTheory.ParahoricConjugateOpen.relIndex_conj_parahoric
  | (apply _root_.GlobalTheory.ParahoricConjugateOpen.relIndex_conj_parahoric <;> assumption)
  | (intros; apply _root_.GlobalTheory.ParahoricConjugateOpen.relIndex_conj_parahoric <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ParahoricConjugateOpen.relIndex_conj_parahoric <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ParahoricConjugateOpen.relIndex_conj_parahoric ..)

end GlobalTheory.ParIdx
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_twoBlockParahoric_conj_torusDiagElement : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ),
    (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom).relIndex (parahoric k A D) : ℝ) =
      (resCard k : ℝ) ^ ((Fintype.card A : ℤ) * sumAbs e) *
        (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom).relIndex (KO k D) : ℝ) := by
  atlas_forward_decl GlobalTheory.ParIdx.relIndex_parahoric_conj_mtor
