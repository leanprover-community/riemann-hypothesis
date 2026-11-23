module

public import GroundTheory.GlobalFields.IdeleGroups.LocalConditionIndex
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import GroundTheory.GlobalFields.ExistenceTheorem.IndexRangePowMonoidHomAdicCompletionMulNorm
public import GroundTheory.GlobalFields.FirstInequality
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import GroundTheory.GlobalFields.KummerTheory.KummerIndexLemma.HasEnoughRootsOfUnityOfRingHom

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh IdeleGroup
  KummerIndex

universe u

section Power

variable {K : Type u} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

theorem index_map_powerSubgroup (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤) :
    ((powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).map (IdeleClassGroup.mk K)).index =
      n ^ (S.card + Fintype.card (InfinitePlace K)) :=
  firstInequality.index_map_powerSubgroup S hS hJ

end Power

section Prime

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity K p]

end Prime

end GroundTheory.Global
