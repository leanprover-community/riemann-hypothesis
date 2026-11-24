module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypersurfaceDiffIsPreirreducibleOfNoSplittingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoSplittingFactorisationOfPderivNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplittingAbsenceSpreadsStatement
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
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem hypersurface_part_preirreducible_spreads : ∀ (A : Type) [CommRing A] (σ : Type) [Finite σ] (f g : MvPolynomial σ A) (i : σ), (∀ (k : Type) [Field k] (ψ : A →+* k), MvPolynomial.map ψ f ≠ 0) → (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : σ → k), MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv i (MvPolynomial.map ψ f)) ≠ 0) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map φ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map φ g}) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map ψ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map ψ g}) := by
  intro A _ σ _ f g i h0 hd Ω _ _ φ hirr
  have h3 := GlobalTheory.T.no_splitting_factorisation_of_pderiv_ne_zero Ω σ (MvPolynomial.map φ f) (MvPolynomial.map φ g) i f.totalDegree
    (hd Ω φ) hirr
  obtain ⟨a, I, ha, hI, h⟩ := GlobalTheory.T.splitting_absence_spreads_alt A σ f g f.totalDegree Ω φ h3
  refine ⟨a, I, ha, hI, fun k _ _ ψ hψa hψI => ?_⟩
  refine GlobalTheory.T.hypersurface_diff_isPreirreducible_of_no_splitting k σ (MvPolynomial.map ψ f) (MvPolynomial.map ψ g) f.totalDegree
    (h0 k ψ) ?_ (h k ψ hψa hψI)
  exact Finset.sup_mono (MvPolynomial.support_map_subset ψ f)

end GlobalTheory
