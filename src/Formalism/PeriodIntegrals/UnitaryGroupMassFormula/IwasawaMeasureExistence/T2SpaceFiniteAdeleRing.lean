module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology

variable {F : Type} [Field F] [NumberField F]

theorem val_algebraMap_F (v : HeightOneSpectrum (𝓞 F)) (t : F) :
    Valued.v (algebraMap F (v.adicCompletion F) t) = v.valuation F t := by
  rw [algebraMap_adicCompletion]
  simp [valuedAdicCompletion_eq_valuation']

theorem exists_int_near (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (hx : Valued.v x ≤ 1) :
    ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1 := by
  apply PI.WAU.exists_int_near <;> assumption

def toOv (v : HeightOneSpectrum (𝓞 F)) : 𝓞 F →+* Valued.integer (v.adicCompletion F) :=
  ((algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)).codRestrict _ (fun a => by
    show Valued.v (_ : v.adicCompletion F) ≤ 1
    simp only [RingHom.comp_apply]
    rw [val_algebraMap_F, valuation_of_algebraMap]
    exact intValuation_le_one v a)

theorem toOv_coe (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    ((toOv v a : Valued.integer (v.adicCompletion F)) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := rfl

theorem isUnit_integer_iff (v : HeightOneSpectrum (𝓞 F)) (x : Valued.integer (v.adicCompletion F)) :
    IsUnit x ↔ Valued.v (x : v.adicCompletion F) = 1 :=
  (Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)).isUnit_iff_valuation_eq_one

theorem finite_residue (v : HeightOneSpectrum (𝓞 F)) :
    Finite (IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F))) := by
  apply PI.WAU.finite_residue <;> assumption

theorem compactSpace_integer (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (Valued.integer (v.adicCompletion F)) := by
  rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  refine ⟨?_, ?_, finite_residue v⟩
  · exact (Valued.isClosed_integer (R := v.adicCompletion F)).completeSpace_coe
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))

theorem isCompact_Ov (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have := compactSpace_integer v
  exact isCompact_iff_compactSpace.mpr this

def Ohat (F : Type) [Field F] [NumberField F] : Set (FiniteAdeleRing (𝓞 F) F) :=
  {a | ∀ v, a v ∈ v.adicCompletionIntegers F}

theorem isOpen_Ohat : IsOpen (Ohat F) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ ↦ Valued.isOpen_valuationSubring _)

instance compactSpace_Ov' (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  isCompact_iff_compactSpace.mp (isCompact_Ov v)

theorem isCompact_Ohat : IsCompact (Ohat F) := by
  have hc : Continuous (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) :=
    RestrictedProduct.isEmbedding_structureMap.continuous
  have : Ohat F = Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) := by
    ext a
    constructor
    · intro ha
      exact ⟨fun v => ⟨a v, ha v⟩, rfl⟩
    · rintro ⟨x, rfl⟩ v
      exact (x v).2
  rw [this]
  exact isCompact_range hc

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

open scoped TensorProduct

variable {F E B : Type} [Field F] [Field E] [Algebra F E] [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)


variable [TopologicalSpace B] [IsTopologicalRing B]

variable {b}
variable {X : Type*} [TopologicalSpace X]


end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

variable {F : Type} [Field F] [NumberField F]

theorem ohat_zero : (0 : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F :=
  fun v => by
    show (0 : v.adicCompletion F) ∈ _
    exact zero_mem _


variable {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

variable {b}


end PI.IwaMeasEx.Wau

end
