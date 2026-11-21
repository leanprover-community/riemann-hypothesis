import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.WeilBound.CoreStatements.HodgeTatePoints.DegLeOfEquiv

section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem subDeg_le_zero_of_trivial : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (b : Module.Basis (Fin n) K V) (L : C.I → AddSubgroup V) (W : Submodule K V), (∀ i, IsLatOf C i b (L i)) → subDeg C L W ≤ 0 :=
  @PositivityTheory.HtPt.Ch.subdeg_trivial

end GlobalTheory.CompanionTheory.Ar.Crv
end

open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_degree_nonpos_trivial_lattice : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (b : Module.Basis (Fin n) K V) (L : C.I → AddSubgroup V) (W : Submodule K V), (∀ i, IsLatOf C i b (L i)) → subDeg C L W ≤ 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_zero_of_trivial
