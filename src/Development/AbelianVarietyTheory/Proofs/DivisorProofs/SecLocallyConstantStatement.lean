module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Mathlib.Topology.LocallyConstant.Algebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecLocallyConstant
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.sec_exists_of_isLocallyConstant_locallyConstant : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (B : Type) [CommRing B], (∀ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), IsLocallyConstant (fun x : X => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t)) ∧ Function.Injective (fun (t : Sec F (Spec (CommRingCat.of (LocallyConstant X B)))) (x : X) => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t) ∧ ∀ ψ : X → Sec F (Spec (CommRingCat.of B)), IsLocallyConstant ψ → ∃ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), ∀ x, Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t = ψ x := by
  first | (exact @GlobalTheory.EtC.sec_locallyConstant) | (exact GlobalTheory.EtC.sec_locallyConstant) | (intros; apply GlobalTheory.EtC.sec_locallyConstant  <;> assumption)
