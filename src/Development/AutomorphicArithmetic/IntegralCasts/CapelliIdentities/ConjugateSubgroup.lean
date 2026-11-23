module

public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.RightOfFd
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem UpperTheory.Reformulated.B.ConjugateSubgroup.conj_sub :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G]
    [inst_3 : MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    {Γ A : Subgroup G},
    IsClosed (↑A : Set G) →
      PositivityTheory.ThKEnd.Two.Lat (Γ.subgroupOf A) →
        ∀ {f c : G → ℂ},
          PositivityTheory.ThKEnd.Two.IsAv (Γ.subgroupOf A) Subtype.val f c →
            ∀ {γ : G},
              γ ∈ Γ →
                (∀ u ∈ A, γ⁻¹ * u * γ ∈ A) →
                  (∀ u ∈ A, γ * u * γ⁻¹ ∈ A) →
                    (∀ (x : G), f (γ * x) = f x) →
                      ∀ (x : G),
                        c (γ * x) =
                          c
                            x := by
  intro G _ _ _ _ _ _ _ _ Γ A hA L f c h γ hγ h1 h2 hf x
  haveI : LocallyCompactSpace A := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology A := Topology.IsInducing.subtypeVal.secondCountableTopology
  let e : A ≃ₜ* A :=
    { toFun := fun u => ⟨γ⁻¹ * u * γ, h1 u u.2⟩
      invFun := fun u => ⟨γ * u * γ⁻¹, h2 u u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := Continuous.subtype_mk (by fun_prop) _
      continuous_invFun := Continuous.subtype_mk (by fun_prop) _ }
  refine PositivityTheory.ThKEnd.Two.IsAv.conj (ι := A.subtype) L h e (fun u => ?_) (fun u => ?_) hf x
  · exact (Γ.mul_mem_cancel_right hγ).trans (Γ.mul_mem_cancel_left (inv_mem hγ))
  · exact show (u : G) * γ = γ * (γ⁻¹ * u * γ) by group
