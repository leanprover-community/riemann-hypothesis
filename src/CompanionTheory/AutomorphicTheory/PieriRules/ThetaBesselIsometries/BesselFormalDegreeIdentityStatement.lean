module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselFormalDegreeIdentity
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

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.bessel_formal_degree_identity : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (dd : ℝ), R.IsDG ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ (x y x' y' : R.H) (X X' : Wq →L[ℂ] Wp) (p : B.SS k r), D.inSS p → Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) (Matrix.of g)) (⟪x', R.σ (Matrix.of g) y'⟫_ℂ • X')) D.μG ∧ B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p = ⟪y', R.σ (JF.sR p) y⟫_ℂ * ⟪R.σ (JF.sL p) x, x'⟫_ℂ / (dd : ℂ) * B.hsInner ((D.π (Matrix.of p.1.1)).comp (X.comp (D.π' (Matrix.of p.2.1)⁻¹))) X' := by
  first | exact @GlobalTheory.BesselPhi.Ph_coeff | exact GlobalTheory.BesselPhi.Ph_coeff | (intros; apply GlobalTheory.BesselPhi.Ph_coeff <;> assumption)
