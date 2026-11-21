import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.TemperedEigenvalueNorms.AddOneLeOfPrecedes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentQuotientOfTwoSegment
import BuildAid.D4

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace PositivityTheory.UdReth2

section SpehAux


def piTensorInt {α : Type} {Γ Y Z : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] [∀ a, AddCommGroup (Z a)] [∀ a, Module ℂ (Z a)]
    {π : ∀ a, Representation ℂ (Γ a) (Y a)} {σ : ∀ a, Representation ℂ (Γ a) (Z a)}
    (f : ∀ a, (π a).IntertwiningMap (σ a)) : (piTensor π).IntertwiningMap (piTensor σ) where
  toLinearMap := PiTensorProduct.map fun a => (f a).toLinearMap
  isIntertwining' g := by
    ext x
    simp [Representation.IntertwiningMap.isIntertwining]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]



end SpehAux


end PositivityTheory.UdReth2
