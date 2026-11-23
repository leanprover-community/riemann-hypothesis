module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurvePointDVR
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
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem NormalCurvePointDVR.proof : NormalCurvePointDVR.Statement := by
  intro σ _ I w hI hic hdim hw
  have : I.IsPrime := hI
  let m : Ideal (MvPolynomial σ ℂ) := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)
  let S := Localization.AtPrime m
  let T := S ⧸ I.map (algebraMap (MvPolynomial σ ℂ) S)
  let A := MvPolynomial σ ℂ ⧸ I
  have hIm : I ≤ m := fun f hf ↦ RingHom.mem_ker.2 (hw f hf)
  let P : Ideal A := m.map (Ideal.Quotient.mk I)
  have hmem : ∀ f, Ideal.Quotient.mk I f ∈ P ↔ f ∈ m := fun f ↦ Ideal.mem_quotient_iff_mem hIm
  have hP : P.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIm)

  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.2 (by rw [hdim])
  have : Ring.DimensionLEOne A := ⟨fun hp0 hp ↦ hp.isMaximal_of_ne_bot hp0⟩
  have : IsDedekindRing A := { toIsIntegralClosure := hic }

  have hP0 : P ≠ ⊥ := by
    intro h0
    have hmI : m ≤ I := fun f hf ↦ by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_bot, ← h0]
      exact (hmem f).2 hf
    have hmax : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun z ↦ ⟨C z, by simp⟩)
    have hfield : IsField A := (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).1 (le_antisymm hIm hmI ▸ hmax)
    have := ringKrullDim_eq_zero_of_isField hfield
    rw [hdim] at this
    exact_mod_cast this

  have hsub : Algebra.algebraMapSubmonoid A m.primeCompl = P.primeCompl := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact fun h ↦ hf ((hmem f).1 h)
    · intro hx
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨f, fun h ↦ hx ((hmem f).2 h), rfl⟩
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid A m.primeCompl) T := inferInstance
  have hlocP : IsLocalization.AtPrime T P := by
    change IsLocalization P.primeCompl T
    rw [← hsub]
    exact hloc
  have hdom : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T (M := P.primeCompl)
    P.primeCompl_le_nonZeroDivisors
  exact ⟨hdom, IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP0 T⟩

end

end GroundTheory.Heights₂.Heights
