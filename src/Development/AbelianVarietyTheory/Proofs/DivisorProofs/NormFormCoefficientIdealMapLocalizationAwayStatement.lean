module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
public import Mathlib.RingTheory.Localization.Away.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFormCoefficientIdealMapLocalizationAway
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
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.normFormCoefficientIdeal_map_localizationAway : ∀ (A K L B A' B' : Type) [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A K] [Algebra B L] [Algebra A' K] [Algebra B' L]
    [Algebra A A'] [Algebra B B'] [Algebra A B] (f : A) [IsLocalization.Away f A']
    [IsLocalization.Away (algebraMap A B f) B'],
    (algebraMap A' K).comp (algebraMap A A') = algebraMap A K →
    (algebraMap B' L).comp (algebraMap B B') = algebraMap B L →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp (algebraMap A B) →
    Function.Injective (algebraMap A' K) →
    (∀ {m : ℕ} (g : Fin m → B) s,
      (GlobalTheory.NormSheaf.normForm K L (fun i => algebraMap B L (g i))).coeff s ∈ (algebraMap A K).range) →
    ∀ J : Ideal B, (GlobalTheory.NormSheaf.normIdeal A K L B J).map (algebraMap A A') =
      GlobalTheory.NormSheaf.normIdeal A' K L B' (J.map (algebraMap B B')) := by
  first | exact @GlobalTheory.NormSheaf.normIdeal_map_away | exact GlobalTheory.NormSheaf.normIdeal_map_away | (intros; apply GlobalTheory.NormSheaf.normIdeal_map_away <;> assumption)
