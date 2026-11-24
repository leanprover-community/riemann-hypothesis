module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteKTypeDecomposition
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm
import Development.WeilBound.ThetaLifts.LatticeBasics.FarRight
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

theorem _root_.GlobalTheory.T.finite_K_type_decomposition : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ K P : Subgroup G) (c : G → ℂ) (η : G → ℝ), IsCh Γ P c → (∀ r ∈ P, r ∈ K → η r = 0) → (∀ p ∈ P, ∀ q ∈ P, η (p * q) = η p + η q) → ∀ (f : G → ℂ) (u : ℂ), Continuous f → (∀ p ∈ P, ∀ x, f (p * x) = c p * Complex.exp (u * η p) * f x) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * (k : G)))) → ∃ (d : ℕ) (ρ : K →* ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ))) (w : Fin d → ℂ) (e : (Fin d → ℂ) →L[ℂ] ℂ), Continuous ρ ∧ w ∈ secSp K P c ρ ∧ ∀ k : K, e (ρ k⁻¹ w) = f k := by
  first | exact @GlobalTheory.CompanionTheory.SiegelRep.exists_rep | exact GlobalTheory.CompanionTheory.SiegelRep.exists_rep | (intros; apply GlobalTheory.CompanionTheory.SiegelRep.exists_rep <;> assumption)
