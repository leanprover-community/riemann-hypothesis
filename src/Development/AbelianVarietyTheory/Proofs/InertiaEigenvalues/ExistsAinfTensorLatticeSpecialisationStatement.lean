module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfTensorLatticeSpecialisation
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

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ainf_tensor_lattice_specialisation : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f n : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (θ : Ainf l →ₐ[ℤ_[l]] OC l), IsMat K LL T M A → IsThetaShift AI n θ → ∃ Φ : TW (RA LL) T →+ (Fin d → PadicComplex l), (∀ (r : RA LL) (z : TW (RA LL) T), Φ (r • z) = (lam o A (thR LL θ r)).mulVec (Φ z)) ∧ (∀ z i, ‖Φ z i‖ ≤ 1) ∧ (∀ (g : ↥(GK K)) (z : TW (RA LL) T), Φ (TWact (gRA AI LL (g : GQ l)) T g z) = (M (g : GQ l)).mulVec (fun i => AI.actC (g : GQ l) (Φ z i))) ∧ ∀ j, ∃ t : ↥T.L.T, Φ ((1 : RA LL) ⊗ₜ[↥(OL LL)] t) = Pi.single j 1 := by
  exact @GlobalTheory.Cyc.Decomp.exists_specPhi
