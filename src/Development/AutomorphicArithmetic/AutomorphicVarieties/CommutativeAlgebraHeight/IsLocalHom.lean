module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open IsLocalRing

namespace UpperTheory.V.CA

structure IsCL (O R : Type) [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] : Prop where
  noeth : IsNoetherianRing R
  complete : IsAdicComplete (maximalIdeal R) R
  isLocalHom : IsLocalHom (algebraMap O R)
  res_fin : Module.Finite O (ResidueField R)

theorem IsCL.of_isCO (O R : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Alg.IsCO O R] :
    IsCL O R := by
  refine ⟨inferInstance, UpperTheory.V.Alg.IsCO.complete (O := O), UpperTheory.V.Alg.IsCO.isLocalHom, ?_⟩
  refine Module.Finite.of_surjective (Algebra.linearMap O (ResidueField R)) ?_
  intro y
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨a, ha⟩ := UpperTheory.V.Alg.IsCO.res_surj (O := O) r
  refine ⟨a, ?_⟩
  rw [Algebra.linearMap_apply, IsScalarTower.algebraMap_apply O R (ResidueField R),
    ResidueField.algebraMap_eq, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have h' := (maximalIdeal R).neg_mem ha
  rwa [neg_sub] at h'

section Cpl

variable {C : Type} [CommRing C] (x : Ideal C) [x.IsPrime]

abbrev Cpl : Type := AdicCompletion (maximalIdeal (Localization.AtPrime x)) (Localization.AtPrime x)

def dimAt (I : Ideal C) : WithBot ℕ∞ :=
  ringKrullDim (Localization.AtPrime x ⧸ I.map (algebraMap C (Localization.AtPrime x)))

end Cpl

structure IsCplAt {C : Type} [CommRing C] (x : Ideal C) (R : Type) [CommRing R] [Algebra C R] [IsLocalRing R] :
    Prop where
  noeth : IsNoetherianRing R
  complete : IsAdicComplete (maximalIdeal R) R
  comap_pow : ∀ n : ℕ, (maximalIdeal R ^ n).comap (algebraMap C R) = x ^ n
  dense : ∀ (n : ℕ) (r : R), ∃ c : C, r - algebraMap C R c ∈ maximalIdeal R ^ n

end UpperTheory.V.CA
