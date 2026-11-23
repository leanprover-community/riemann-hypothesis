module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
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
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)

theorem dense_compl_coordDiv {D : ℕ} (S : Finset (Fin D)) : Dense (coordDiv S)ᶜ := by
  have h : (coordDiv S)ᶜ = ⋂ i ∈ (S : Set (Fin D)), (fun z : Fin D → ℂ => z i) ⁻¹' ({0}ᶜ) := by
    ext z
    simp [coordDiv]
  rw [h]
  refine dense_biInter_of_isOpen (fun i _ => ?_) S.countable_toSet (fun i _ => ?_)
  · exact isOpen_compl_singleton.preimage (continuous_apply i)
  · exact (dense_compl_singleton (0 : ℂ)).preimage (isOpenMap_eval i)

theorem RegYoDense.proof : RegYoDense.Statement := by
  intro X _ D A R
  rw [dense_iff_inter_open]
  rintro U hU ⟨x, hxU⟩
  have hxj : x ∈ bdDom R (bdIdx R x) := mem_bdDom_bdIdx R x
  set j := bdIdx R x
  have hO : IsOpen ((R.ψ j) '' ((R.ψ j).source ∩ (U ∩ bdDom R j))) :=
    (R.ψ j).isOpen_image_source_inter (hU.inter (isOpen_bdDom R j))
  have hne : ((R.ψ j) '' ((R.ψ j).source ∩ (U ∩ bdDom R j))).Nonempty :=
    ⟨R.ψ j x, x, ⟨hxj.1, hxU, hxj⟩, rfl⟩
  obtain ⟨z, ⟨y, ⟨hys, hyU, hyD⟩, rfl⟩, hz⟩ :=
    (dense_compl_coordDiv (R.S j)).inter_open_nonempty _ hO hne
  have hYo := (R.mem_Yo_iff j (R.ψ j y) hyD.2).2 hz
  rw [(R.ψ j).left_inv hys] at hYo
  exact ⟨y, hyU, hYo⟩

end GroundTheory.Heights₂.Heights.AnalyticLimit
