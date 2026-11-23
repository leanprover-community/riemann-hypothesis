module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexPairingTensorUniversalProperty
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

theorem _root_.GlobalTheory.T.sheafComplexPairing_tensor_universal_property : ∀ (R S : Type) [CommRing R] [CommRing S] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g w x)) → ∃ φ : ∀ U : Scheme.{0}, Sec (K.X w) U →+ Sec M U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) ∧ ∀ U x, φ U (τ.lift U w x) = b U x := by
  first | exact @GlobalTheory.EtC.tens_fam | exact GlobalTheory.EtC.tens_fam | (intros; apply GlobalTheory.EtC.tens_fam <;> assumption)
