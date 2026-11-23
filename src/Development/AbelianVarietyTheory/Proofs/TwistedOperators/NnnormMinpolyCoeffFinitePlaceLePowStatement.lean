module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NnnormMinpolyCoeffFinitePlaceLePow
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

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal
open Classical

theorem _root_.GlobalTheory.T.nnnorm_minpoly_coeff_finitePlace_le_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x : E) (v : HeightOneSpectrum (𝓞 F)) (j : ℕ), ‖algebraMap F (v.adicCompletion F) ((minpoly F x).coeff j)‖₊ ≤ max 1 (absFin F v ((1 : v.adicCompletion F) ⊗ₜ[F] x)) ^ Module.finrank F E := by
  first | exact @GlobalTheory.CoefHeight.nnnorm_coeff_minpoly_le | exact GlobalTheory.CoefHeight.nnnorm_coeff_minpoly_le | (intros; apply GlobalTheory.CoefHeight.nnnorm_coeff_minpoly_le <;> assumption)
