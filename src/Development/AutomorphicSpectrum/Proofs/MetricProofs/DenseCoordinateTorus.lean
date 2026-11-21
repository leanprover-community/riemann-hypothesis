import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
import BuildAid.ForwardExisting

section
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

theorem dense_forall_coord_ne_zero : ∀ n : ℕ, Dense {z : Fin n → ℂ | ∀ i, z i ≠ 0} := by
  intro n
  have h : {z : Fin n → ℂ | ∀ i, z i ≠ 0} = Set.pi Set.univ (fun _ => ({0}ᶜ : Set ℂ)) := by
    ext z
    simp
  rw [h]
  exact dense_pi Set.univ (fun _ _ => dense_compl_singleton 0)

end GlobalTheory.CompanionTheory.Ar.PB.Flat
end

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_coordinate_torus : ∀ n : ℕ, Dense {z : Fin n → ℂ | ∀ i, z i ≠ 0} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.Flat.dense_forall_coord_ne_zero
