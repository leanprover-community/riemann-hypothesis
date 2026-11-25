module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DetAdmA
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear

@[expose] public section

noncomputable section

namespace PI.VolStabS.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabS.PositiveNearLattice MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct

section Borel

variable {F : Type} [Field F] [NumberField F]

instance borel_Ainf : BorelSpace (Ainf F) := ⟨rfl⟩
instance borel_Af : BorelSpace (Af F) := ⟨rfl⟩
instance borel_tens {E : Type} [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] : BorelSpace (R ⊗[F] E) := ⟨rfl⟩

end Borel

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

export PI.VolStabSW.DeterminantAdmissible (isCompact_intV isClopen_intV)

instance lc_Fv : LocallyCompactSpace (Fv F v) :=
  (isCompact_intV v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((isClopen_intV v).isOpen.mem_nhds (zero_mem (v.adicCompletionIntegers F)))

theorem isClopen_translate (t : Fv F v) :
    IsClopen ((Homeomorph.subRight t) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) := by
  exact (isClopen_intV v).preimage (Homeomorph.subRight t).continuous

theorem isCompact_translate (t : Fv F v) :
    IsCompact ((Homeomorph.subRight t) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) := by
  exact (Homeomorph.subRight t).isCompact_preimage.mpr (isCompact_intV v)

theorem mem_translate (t : Fv F v) :
    t ∈ (Homeomorph.subRight t) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
  simp

end Local

section Box1

variable {F : Type} [Field F] [NumberField F]

end Box1

end PI.VolStabS.DeterminantAdmissible
