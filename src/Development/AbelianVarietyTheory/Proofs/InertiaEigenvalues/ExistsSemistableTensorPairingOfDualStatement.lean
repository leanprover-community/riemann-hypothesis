module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableTensorPairingOfDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_semistable_tensor_pairing_of_dual : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → ∃ pr : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] Bst P, (∀ x y, pr (phiV P ℚ_[l] V x) (phiV P ℚ_[l] V' y) = phiSt P (pr x y)) ∧ (∀ x y, pr (monV P ℚ_[l] V x) y + pr x (monV P ℚ_[l] V' y) = monSt P (pr x y)) ∧ (∀ (g : ↥(GK K)) x y, pr (stRep P ρ g x) (stRep P ρ' g y) = ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) • actSt P (g : GQ l) (pr x y)) ∧ (∀ a x y, pr (onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) x) y = a * pr x y) ∧ ∀ y, (∀ v : V, pr (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) y = 0) → y = 0 := by
  first | exact @GlobalTheory.PMon.StPairing.exists_stPairing | exact GlobalTheory.PMon.StPairing.exists_stPairing | (intros; apply GlobalTheory.PMon.StPairing.exists_stPairing <;> assumption)
