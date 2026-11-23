module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenFibresPreirreducibleSmooth
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_basicOpen_fibres_preirreducible_smooth : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Algebra.Smooth A B → ∀ (q : PrimeSpectrum B) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω], q.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A Ω) → PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) → ∃ (b : B) (a : A) (I : Finset A), b ∉ q.asIdeal ∧ algebraMap A B a ∉ q.asIdeal ∧ (∀ c ∈ I, algebraMap A B c ∈ q.asIdeal) ∧ ∀ t : PrimeSpectrum A, a ∉ t.asIdeal → (∀ c ∈ I, c ∈ t.asIdeal) → IsPreirreducible {r : PrimeSpectrum B | r.asIdeal.comap (algebraMap A B) = t.asIdeal ∧ b ∉ r.asIdeal} := by
  first | exact @GlobalTheory.exists_basicOpen_fibres_preirreducible | exact GlobalTheory.exists_basicOpen_fibres_preirreducible | (intros; apply GlobalTheory.exists_basicOpen_fibres_preirreducible <;> assumption)
