module

public import GroundTheory.GlobalFields.IdeleClassGroup.IdeleClassMapIdeleClassMap
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.MaxUnramifiedOutside
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

namespace PicInf

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))}

def levelOfField (L : IntermediateField K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) [FiniteDimensional K.1 L] :
    FiniteSubfield :=
  ⟨(L.map (maxUnramifiedOutside K.1 ℚ̄ S).val).restrictScalars ℚ, by
    have := K.2
    have : FiniteDimensional K.1 (L.map (maxUnramifiedOutside K.1 ℚ̄ S).val) :=
      LinearEquiv.finiteDimensional (L.equivMap (maxUnramifiedOutside K.1 ℚ̄ S).val).toLinearEquiv
    have : FiniteDimensional ℚ (L.map (maxUnramifiedOutside K.1 ℚ̄ S).val) :=
      Module.Finite.trans K.1 (L.map (maxUnramifiedOutside K.1 ℚ̄ S).val)
    exact this⟩

variable (L : IntermediateField K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) [FiniteDimensional K.1 L]

theorem mem_levelOfField {z : ℚ̄} :
    z ∈ (levelOfField L).1 ↔ ∃ w ∈ L, ((w : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = z :=
  Iff.rfl

instance fact_le_levelOfField : Fact (K ≤ levelOfField L) :=
  ⟨fun z hz => (mem_levelOfField L).2 ⟨algebraMap K.1 _ ⟨z, hz⟩, L.algebraMap_mem _, rfl⟩⟩

theorem mem_maxUnramifiedOutside_of_mem_levelOfField {z : ℚ̄} (hz : z ∈ (levelOfField L).1) :
    z ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
  obtain ⟨w, -, rfl⟩ := (mem_levelOfField L).1 hz
  exact w.2

end

end PicInf

end GroundTheory.ProfCoh
