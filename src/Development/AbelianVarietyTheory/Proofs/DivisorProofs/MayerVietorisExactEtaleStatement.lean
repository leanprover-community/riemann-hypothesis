module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayHomCompAlgebraMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisExactEtale
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

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

theorem _root_.GlobalTheory.T.mayer_vietoris_exact_etale : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), IsNbhd A A' f → ∀ n i : ℤ, ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A'' : Type) [CommRing A''] [Algebra A A''] [Algebra.Etale A A''] (φ : A' →ₐ[A] A''), IsNbhd A A'' f → ∀ z, pull _ (spMap (awayHom φ f)) _ _ z = 0 → δ z = 0 := by
  first | (exact @GlobalTheory.EtC.ExcisionNat.excision_natural) | (exact GlobalTheory.EtC.ExcisionNat.excision_natural) | (intros; apply GlobalTheory.EtC.ExcisionNat.excision_natural <;> assumption)
