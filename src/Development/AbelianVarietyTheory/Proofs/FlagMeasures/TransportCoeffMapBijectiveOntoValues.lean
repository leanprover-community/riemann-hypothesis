module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjLinearOntoOfInjectiveOfLeRange
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivariantUnitaryCoefficientMapOntoStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem transport_J_bijective_onto :
    ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F),
      Function.Injective Tr.J ∧ ∀ p ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0), ∃ ξ, Tr.J ξ = p := by
  intro D X u F Tr
  obtain ⟨c, -⟩ := F.cls0.y_bij.2 (Quotient.mk'' 1)
  have hinj : Function.Injective Tr.J := by
    intro ξ η h
    have h1 := Tr.J_isom c ξ η
    have h2 := Tr.J_isom c ξ ξ
    have h3 := Tr.J_isom c η ξ
    have h4 := Tr.J_isom c η η
    rw [h] at h1 h2 h3
    rw [h4] at h1 h2 h3
    have h0 : ⟪ξ - η, ξ - η⟫_ℂ = 0 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, ← h1, ← h2, ← h3]
      ring
    exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)
  refine ⟨hinj, ?_⟩
  obtain ⟨J₀, -, hJ₀⟩ := GlobalTheory.T.exists_equivariant_unitary_coefficientMap_onto D X u F Tr.wt ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  exact GlobalTheory.conjLinear_onto_of_injective_of_le_range (X.Vpi u) _ _ J₀ Tr.J hJ₀ hinj Tr.J_val

end GlobalTheory
