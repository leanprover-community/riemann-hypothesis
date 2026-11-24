module

public import Development.EtaleCohomology.EtaleSheaves.LeafSmoothOfNormalPf
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafRelDimOnePf

theorem exists_ne_generic {C : Scheme.{0}} [IsIntegral C] (hd : topologicalKrullDim C = 1) :
    ∃ x : C, x ≠ genericPoint C := by
  by_contra h
  push Not at h
  have : Subsingleton C := ⟨fun a b => (h a).trans (h b).symm⟩
  have : DiscreteTopology C := inferInstance
  have := topologicalKrullDim_zero_of_discreteTopology C
  rw [hd] at this
  exact absurd this (by decide)

theorem isField_top (Ω : Type) [Field Ω] : IsField Γ(Sp Ω, ⊤) :=
  MulEquiv.isField (Field.toIsField Ω)
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.toMulEquiv

theorem chart (Ω : Type) [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) [IsIntegral C]
    (hd : topologicalKrullDim C = 1) (U : (Sp Ω).Opens) (V : C.Opens) (hV : IsAffineOpen V)
    (x : C) (hx : x ∈ V) (hxη : x ≠ genericPoint C) (e : V ≤ c ⁻¹ᵁ U)
    (hs : (c.appLE U V e).hom.IsStandardSmooth) :
    RingHom.IsStandardSmoothOfRelativeDimension 1 (c.appLE U V e).hom := by
  have hU : U = ⊤ := by
    ext p
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have : p = c x := Subsingleton.elim _ _
    subst this
    exact e hx
  subst hU
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  let : Field Γ(Sp Ω, ⊤) := (isField_top Ω).toField
  let : Algebra Γ(Sp Ω, ⊤) Γ(C, V) := (c.appLE ⊤ V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hs.out
  have : Algebra.IsStandardSmoothOfRelativeDimension P.dimension Γ(Sp Ω, ⊤) Γ(C, V) :=
    P.isStandardSmoothOfRelativeDimension rfl
  have h1 := GlobalTheory.AffinePoints.ringKrullDim_eq_of_isStandardSmooth (K := Γ(Sp Ω, ⊤)) (A := Γ(C, V))
    (d := P.dimension)
  have hle : ringKrullDim Γ(C, V) ≤ 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← hd]
    exact hV.fromSpec.isOpenEmbedding.isInducing.topologicalKrullDim_le
  have hne : ringKrullDim Γ(C, V) ≠ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 Γ(C, V) := Ring.krullDimLE_iff.mpr (by rw [h0]; rfl)
    have hF := Ring.KrullDimLE.isField_of_isDomain (R := Γ(C, V))
    let := hF.toField
    have hη : genericPoint C ∈ V :=
      ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr ⟨x, by simp, hx⟩
    have hx' : x ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hx
    have hη' : genericPoint C ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hη
    obtain ⟨a, rfl⟩ := hx'
    obtain ⟨b, hb⟩ := hη'
    apply hxη
    rw [← hb]
    have key : ∀ p : PrimeSpectrum Γ(C, V), p.asIdeal = ⊥ := by
      intro p
      have hp := p.isPrime
      exact Ideal.eq_bot_of_prime _
    congr 1
    exact PrimeSpectrum.ext ((key a).trans (key b).symm)
  rw [h1] at hle hne
  have h2 : P.dimension ≤ 1 := by exact_mod_cast hle
  have h3 : P.dimension ≠ 0 := by exact_mod_cast hne
  exact P.isStandardSmoothOfRelativeDimension (by omega)

theorem LeafRelDimOne_of : LateralTheory.E.LeafSmoothOfNormalPf.LeafRelDimOne := by
  intro Ω _ C c hC hs hd
  obtain ⟨x₀, hx₀⟩ := exists_ne_generic hd
  constructor
  intro y
  by_cases hy : y = genericPoint C
  · obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth c x₀
    have hyV : y ∈ V := hy ▸ ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr ⟨x₀, by simp, hx⟩
    exact ⟨U, hU, V, hV, hyV, e, chart Ω c hd U V hV x₀ hx hx₀ e h⟩
  · obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth c y
    exact ⟨U, hU, V, hV, hx, e, chart Ω c hd U V hV y hx hy e h⟩

end LateralTheory.E.LeafRelDimOnePf
