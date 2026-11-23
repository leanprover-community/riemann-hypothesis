module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.thetaVectorUpToUnits_thMoved_of_thZero : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) (B.thZero a b) → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' (B.thMoved a b L L') := by
  first | exact @GlobalTheory.MovedVacuum.isVacuum_movedThetaVacuum | exact GlobalTheory.MovedVacuum.isVacuum_movedThetaVacuum | (intros; apply GlobalTheory.MovedVacuum.isVacuum_movedThetaVacuum <;> assumption)
