module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistedIndependenceLemma.TwistedIndependence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorCosetFormula
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig

@[expose] public section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.hecke_operator_coset_formula : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (g : G) (U : Module.End ℂ (fixed π J)), PositivityTheory.Lbc.IsHeckeOpG π J g U → ∀ (r : ℕ) (x : Fin r → G), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ J ⊓ J.map (MulAut.conj g).toMonoidHom) → ∀ v : fixed π J, ((U v : fixed π J) : V) = ((r : ℂ)⁻¹) • ∑ i, π (x i * g) (v : V) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeAvg.heckeG_eq_average | exact GlobalTheory.CompanionTheory.HeckeAvg.heckeG_eq_average | (intros; apply GlobalTheory.CompanionTheory.HeckeAvg.heckeG_eq_average <;> assumption)
