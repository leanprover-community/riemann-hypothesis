module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import GroundTheory.GlobalFields.ComplexMultiplication.ExistsRingEquivExtendOfIsTranscendenceBasis
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Complex.Cardinality
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodA

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

namespace PieceDegreeAlt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {F : Type} [Field F] [Algebra F Ω]




theorem exists_ringEquiv_comp [NumberField F] (sg sg' : F →+* ℂ) :
    ∃ τ : ℂ ≃+* ℂ, (τ : ℂ →+* ℂ).comp sg = sg' := by
  have hc : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  have hΩ : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  have h1 := @GroundTheory.Global.trdeg_eq_cardinalMk_of_countable ℂ _ _ F _ sg.toAlgebra hc hΩ
  have h2 := @GroundTheory.Global.trdeg_eq_cardinalMk_of_countable ℂ _ _ F _ sg'.toAlgebra hc hΩ
  obtain ⟨τ, hτ⟩ := @GroundTheory.Global.exists_ringEquiv_extend_of_trdeg_eq ℂ _ _ F F _ _ sg.toAlgebra sg'.toAlgebra
    (RingEquiv.refl F) (h1.trans h2.symm)
  exact ⟨τ, RingHom.ext fun a => hτ a⟩

end PieceDegreeAlt

open PieceDegreeAlt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
