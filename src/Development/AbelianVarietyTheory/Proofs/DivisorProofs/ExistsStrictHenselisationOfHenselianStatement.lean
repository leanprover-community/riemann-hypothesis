module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisationOfHenselian
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_etale_localization_filtration_strictHenselization : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (Ω : Type) [Field Ω] [Algebra (ResidueField R) Ω] [IsSepClosure (ResidueField R) Ω], ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (_ : HenselianLocalRing S) (_ : IsLocalHom (algebraMap R S)), IsSepClosed (ResidueField S) ∧ Module.Flat R S ∧ (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧ Nonempty (ResidueField S ≃ₐ[ResidueField R] Ω) ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  first | exact @GlobalTheory.exists_strictHenselisation_of_henselian | exact GlobalTheory.exists_strictHenselisation_of_henselian | (intros; apply GlobalTheory.exists_strictHenselisation_of_henselian <;> assumption)
