module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalConditionsOfEquiv
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical


theorem _root_.GlobalTheory.T.local_conditions_of_equiv : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → LocConds θ' K' (e d) f' → LocConds θ K d f := by
  first | exact @GlobalTheory.CompanionTheory.TransportLoc.locConds_of_equiv | exact GlobalTheory.CompanionTheory.TransportLoc.locConds_of_equiv | (intros; apply GlobalTheory.CompanionTheory.TransportLoc.locConds_of_equiv <;> assumption)
