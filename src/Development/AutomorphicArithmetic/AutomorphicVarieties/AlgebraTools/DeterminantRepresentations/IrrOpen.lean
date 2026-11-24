module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GramIff
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.Det.irrOpen :
    ∀ {A G ι : Type} [CommRing A] [Group G] [Fintype ι] [DecidableEq ι] (t : G → A),
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      ∀ (K : Type) [Field K] (φ : A →+* K) (ρ : G →* Matrix ι ι K) (p : PrimeSpectrum A), p.asIdeal = RingHom.ker φ →
        (∀ g, (ρ g).trace = φ (t g)) → (p ∈ U ↔ Submodule.span K (Set.range ρ) = ⊤) := by
  intro A G ι _ _ _ _ t
  refine ⟨⋃ g : ι × ι → G,
      ((PrimeSpectrum.basicOpen (Matrix.of fun a b => t (g a * g b)).det : TopologicalSpace.Opens (PrimeSpectrum A)) :
        Set (PrimeSpectrum A)),
    isOpen_iUnion (fun g => (PrimeSpectrum.basicOpen _).isOpen), ?_⟩
  intro K _ φ ρ p hp htr
  rw [UpperTheory.V.AlgebraTools.Det.gramIff, Set.mem_iUnion]
  apply exists_congr
  intro g
  have hM : φ.mapMatrix (Matrix.of fun a b => t (g a * g b)) =
      Matrix.of fun a b => (ρ (g a * g b)).trace := by
    ext a b
    show φ (t (g a * g b)) = (ρ (g a * g b)).trace
    rw [htr]
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, hp, RingHom.mem_ker, RingHom.map_det, hM]
