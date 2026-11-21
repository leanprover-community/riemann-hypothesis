import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.WeilBound.CoreStatements.HodgeTatePoints.ChSplit

section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem degree_eq_sum_eigen : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L → (∀ a, IsHom C L L (ρ a)) → deg C L = ∑ s, subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) :=
  @PositivityTheory.HtPt.Ch.split_deg

end GlobalTheory.CompanionTheory.Ar.Crv
end

open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_sum_eigen_sub_degrees : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L → (∀ a, IsHom C L L (ρ a)) → deg C L = ∑ s, subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.degree_eq_sum_eigen
