module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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

noncomputable section

namespace GlobalTheory.GaugeEx.StdExist

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

def coordHomeo {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    (R ⊗[F] E) ≃ₜ (Fin d → R) where
  toEquiv := (Algebra.TensorProduct.basis R b).equivFun.toEquiv
  continuous_toFun := by
    haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
    exact IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
  continuous_invFun := by
    haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
    exact IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem isCompact_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  exact isCompact_iff_compactSpace.2 this

theorem isOpen_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
  Valued.isOpen_valuationSubring _

theorem intV_eq {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    intV b v = coordHomeo b (Fv F v) ⁻¹'
      (Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
  ext y
  simp only [intV, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]
  rfl

theorem isCompact_intV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (intV b v) := by
  rw [intV_eq, Homeomorph.isCompact_preimage]
  exact isCompact_univ_pi fun _ => isCompact_integers v

theorem isOpen_intV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (intV b v) := by
  rw [intV_eq]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integers v).preimage
    (coordHomeo b (Fv F v)).continuous

def intK (v : HeightOneSpectrum (𝓞 F)) : TopologicalSpace.PositiveCompacts (Fv F v) where
  carrier := v.adicCompletionIntegers F
  isCompact' := isCompact_integers v
  interior_nonempty' := by
    rw [(isOpen_integers v).interior_eq]
    exact ⟨0, zero_mem _⟩

def intVK {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    TopologicalSpace.PositiveCompacts (Fv F v ⊗[F] E) where
  carrier := intV b v
  isCompact' := isCompact_intV b v
  interior_nonempty' := by
    rw [(isOpen_intV b v).interior_eq]
    exact ⟨0, fun k => by simp⟩

theorem nonempty_stdMeas (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) : Nonempty (StdMeas b) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  exact ⟨{
    lamI := Measure.addHaar
    lamV := fun v => Measure.addHaarMeasure (intVK b v)
    nuI := Measure.addHaar
    nuV := fun v => Measure.addHaarMeasure (intK v)
    haar_lamI := inferInstance
    haar_lamV := fun v => inferInstance
    haar_nuI := inferInstance
    haar_nuV := fun v => inferInstance
    lamV_int := fun v => Measure.addHaarMeasure_self (K₀ := intVK b v)
    nuV_int := fun v => Measure.addHaarMeasure_self (K₀ := intK v) }⟩

end GlobalTheory.GaugeEx.StdExist
