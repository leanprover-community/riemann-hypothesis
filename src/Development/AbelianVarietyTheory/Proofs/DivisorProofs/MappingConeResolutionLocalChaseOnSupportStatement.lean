module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeResolutionLocalChaseOnSupport
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.mappingCone_resolution_localChase_on_support : ∀ (R : Type) [CommRing R] (E : Spc) {F G : Shv R} (φ : F ⟶ G), (∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → Function.Bijective (Sec.map φ (U := U))) → ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b₁ : Sec ((res R F).X (n + 1)) U) (b₂ : Sec ((res R G).X n) U), Sec.map ((res R F).d (n + 1) (n + 2)) b₁ = 0 → Sec.map ((resMap R φ).f (n + 1)) b₁ + Sec.map ((res R G).d n (n + 1)) b₂ = 0 → Loc U fun V g => ∃ (a₁ : Sec ((res R F).X n) V) (a₂ : Sec ((res R G).X (n - 1)) V), Sec.map ((res R F).d n (n + 1)) a₁ = -Sec.res g b₁ ∧ Sec.map ((resMap R φ).f n) a₁ + Sec.map ((res R G).d (n - 1) n) a₂ = Sec.res g b₂ := by
  first | (exact @GlobalTheory.EtC.ConeChase.chase) | (exact GlobalTheory.EtC.ConeChase.chase) | (intros; apply GlobalTheory.EtC.ConeChase.chase  <;> assumption)
