import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenRightInvarianceLocalCoefficient
import BuildAid.ForwardExisting

section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem continuous_castM (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : ℕ} (h : a = b) : Continuous (castM k h) := by
  subst h
  exact continuous_id

theorem continuous_sO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ), Continuous (sO k i t) := by
  intro k _ _ _ _ i t
  exact (GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth.continuous_sEmb k ((i + 1) + t)).comp (continuous_castM k _)

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_shifted_orbit_map : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ), Continuous (sO k i t) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZPhiPG.OntoO.continuous_sO
