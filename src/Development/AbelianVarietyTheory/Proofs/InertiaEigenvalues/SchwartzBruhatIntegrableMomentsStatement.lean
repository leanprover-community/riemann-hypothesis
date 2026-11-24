module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchwartzBruhatIntegrableMoments
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.schwartz_bruhat_integrable_moments : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (F : (Fin m → Ad E) → ℂ),
    F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin m) →
    (∃ L : Set (Fin m → Af E), IsCompact L ∧ ∀ x, F x ≠ 0 → (fun i => pFin E (x i)) ∈ L) ∧
    ∀ k : ℕ, Integrable (fun x => ‖F x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E) := by
  first | exact @GlobalTheory.SchwartzBruhatMoments.compactSupport_and_integrable_moments | exact GlobalTheory.SchwartzBruhatMoments.compactSupport_and_integrable_moments | (intros; apply GlobalTheory.SchwartzBruhatMoments.compactSupport_and_integrable_moments <;> assumption)
