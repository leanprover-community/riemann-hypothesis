module

public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMat
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.HermitianLatticeDegreeEqBundleDegree
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

@[expose] public section

open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors

theorem _root_.GlobalTheory.T.hermitian_lattice_degree_eq_bundle_degree : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (F : Submodule (𝓞 L) B.carrier) (i : ℕ) (f : Fin i → F) (c : F →ₗ[𝓞 L] (Fin i → L)) (Fl : HermLattice L i), LinearIndependent (𝓞 L) f → i = B.rank F → Function.Injective c → (∀ j, c (f j) = Pi.single j 1) → Fl.lattice = LinearMap.range c → (∀ σ, Fl.metric σ = gramMat B σ (fun j => (f j : B.carrier))) → Fl.degree = B.degreeWith F f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lines.degree_eq_degreeWith | exact GlobalTheory.CompanionTheory.Ar.Lines.degree_eq_degreeWith | (intros; apply GlobalTheory.CompanionTheory.Ar.Lines.degree_eq_degreeWith <;> assumption)
