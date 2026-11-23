module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtSobolevContinuousOrbit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hasDerivAt_sobolevContinuous_orbit : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π ℓ → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, HasDerivAt (fun t : ℝ => ℓ (π (NormedSpace.exp (t • X)) v)) (ℓ (dRep π X v)) 0 := by
  first | exact @GlobalTheory.SobOrbit.hasDerivAt_sobCont_orbit | exact GlobalTheory.SobOrbit.hasDerivAt_sobCont_orbit | (intros; apply GlobalTheory.SobOrbit.hasDerivAt_sobCont_orbit <;> assumption)
