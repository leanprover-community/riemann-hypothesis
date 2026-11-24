module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularRingTensorOfFibreLocalRings
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

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.isRegularRing_tensor_of_regular_fibre_localizations : ∀ (S T K : Type) [CommRing S] [CommRing T] [Algebra S T] [IsNoetherianRing T] [Field K] [Algebra S K] (Q : Ideal S), RingHom.ker (algebraMap S K) = Q → (∀ y : K, ∃ a b : S, b ∉ Q ∧ y * algebraMap S K b = algebraMap S K a) → (∀ (n : Ideal T) [n.IsPrime], n.comap (algebraMap S T) = Q → IsRegularLocalRing (Localization.AtPrime n ⧸ (Q.map (algebraMap S T)).map (algebraMap T (Localization.AtPrime n)))) → IsRegularRing (T ⊗[S] K) := by
  first | exact @GlobalTheory.isRegularRing_tensor_of_fibre_localRings | exact GlobalTheory.isRegularRing_tensor_of_fibre_localRings | (intros; apply GlobalTheory.isRegularRing_tensor_of_fibre_localRings <;> assumption)
