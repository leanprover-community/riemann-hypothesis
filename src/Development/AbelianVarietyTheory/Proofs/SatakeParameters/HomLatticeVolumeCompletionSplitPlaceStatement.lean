module

public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.XiOfSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HomLatticeVolumeCompletionSplitPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

theorem _root_.GlobalTheory.T.homLattice_volume_completion_splitPlace : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (v : X.Pl) (j : ℕ) (ρ : D.host.E →+* X.G.P.Qq v) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) → (∀ x : 𝓞 D.host.E, ∃ y : X.G.P.W v, ρ x = algebraMap _ _ y ∧ (x ∈ P.asIdeal ↔ (p : X.G.P.W v) ∣ y)) → (∀ (y : X.G.P.W v) (n : ℕ), ∃ (x : 𝓞 D.host.E) (z : X.G.P.W v), ρ x = algebraMap _ _ (y + (p : X.G.P.W v) ^ n * z)) → ∃ φ : GL3Theta.EP D P ≃+* X.G.P.Qq v, (∀ x : D.host.E, φ (algebraMap _ _ x) = ρ x) ∧ ∀ (M : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (M' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)), IsUnit M.det → IsUnit M'.det → ∀ (N : (X.Pj j).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E)) (N' : (X.Pj (j + 1)).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E)) (S : Set ((X.Pj j).Tup × (X.Pj (j + 1)).Tup)), (∀ q ∈ S, (X.Pj j).IsLatTup q.1 ∧ (X.Pj (j + 1)).IsLatTup q.2 ∧ TaylorLogMetric.admitted D _ _ (N q.1) (N' q.2) ∧ Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N q.1 : Set (Fin ((X.Pj j).m + 1) → D.host.E))) = (X.latAt v j q.1).map ((M.mulVecLin).restrictScalars (X.G.P.W v)) ∧ Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N' q.2 : Set (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))) = (X.latAt v (j + 1) q.2).map ((M'.mulVecLin).restrictScalars (X.G.P.W v))) → ∀ q ∈ S, (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ X.ind v j q.1 q.2 (M'⁻¹ * y.map φ * M) = 1) ∧ ∀ q₀ ∈ S, GL3Theta.volP (GL3Theta.YP D P (N q₀.1) (N' q₀.2)) (GL3Theta.YP D P (N q.1) (N' q.2)) = (p : ℝ) ^ ((X.G.P.n' v : ℤ) * (volE X v j q.1 q.2 - volE X v j q₀.1 q₀.2)) := by
  first | exact @GlobalTheory.VolAt.vol_main | exact GlobalTheory.VolAt.vol_main | (intros; apply GlobalTheory.VolAt.vol_main <;> assumption)
