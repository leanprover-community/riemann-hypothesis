module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIdeleNotMulNorm
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

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_idele_ne_algebraMap_mul_norm_of_not_isSquare : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ a : (AdeleRing (𝓞 F) F)ˣ, ∀ (t : F) (x y : AdeleRing (𝓞 F) F), (a : AdeleRing (𝓞 F) F) ≠ algebraMap F (AdeleRing (𝓞 F) F) t * (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := by
  first | exact @GlobalTheory.QNorm.exists_idele_not_mul_norm | exact GlobalTheory.QNorm.exists_idele_not_mul_norm | (intros; apply GlobalTheory.QNorm.exists_idele_not_mul_norm <;> assumption)
