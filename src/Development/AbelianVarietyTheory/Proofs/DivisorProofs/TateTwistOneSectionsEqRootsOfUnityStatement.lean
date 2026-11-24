module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneSectionsEqRootsOfUnity
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistOne_sections_eq_rootsOfUnity : ∀ (q : ℕ) [NeZero q], ∃ e : ∀ (C : Type) [CommRing C], IsUnit (q : C) → (onRings (tw q 1)).obj (CommRingCat.of C) ≃+ Additive (rootsOfUnity q C), ∀ (C D : Type) [CommRing C] [CommRing D] (φ : C →+* D) (hC : IsUnit (q : C)) (hD : IsUnit (q : D)) (x : (onRings (tw q 1)).obj (CommRingCat.of C)), ((Additive.toMul (e D hD (((onRings (tw q 1)).map (CommRingCat.ofHom φ)).hom x)) : rootsOfUnity q D) : Dˣ) = Units.map φ.toMonoidHom ((Additive.toMul (e C hC x) : rootsOfUnity q C) : Cˣ) := by
  first | (exact @GlobalTheory.EtC.tw_one_mu) | (exact GlobalTheory.EtC.tw_one_mu) | (intros; apply GlobalTheory.EtC.tw_one_mu  <;> assumption)
