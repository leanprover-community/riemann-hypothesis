module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Algebra.Group.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.MultiCentre
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.avg :
    ∀ (H M : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [AddCommGroup M] [Module ℂ M]
      (ρ : H →* Module.End ℂ M) (x : M), (∀ᶠ h in 𝓝 (1 : H), ρ h x = x) →
      ∃ s : Finset H, s.Nonempty ∧ ∀ h, ρ h (∑ k ∈ s, ρ k x) = ∑ k ∈ s, ρ k x := by
  intro H M _ _ _ _ _ _ ρ x hx
  have hmul : ∀ a b : H, ρ (a * b) x = ρ a (ρ b x) := fun a b => by
    rw [map_mul, Module.End.mul_apply]
  let S : Subgroup H :=
    { carrier := {h | ρ h x = x}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ρ a x = x := ha
        have hb' : ρ b x = x := hb
        show ρ (a * b) x = x
        rw [hmul, hb', ha']
      one_mem' := by
        show ρ 1 x = x
        simp
      inv_mem' := fun {a} ha => by
        have ha' : ρ a x = x := ha
        show ρ a⁻¹ x = x
        conv_lhs => rw [← ha']
        rw [← hmul]
        simp }
  have hSo : IsOpen (S : Set H) := Subgroup.isOpen_of_mem_nhds S hx
  haveI : Finite (H ⧸ S) := Subgroup.quotient_finite_of_isOpen S hSo
  haveI : Fintype (H ⧸ S) := Fintype.ofFinite _
  have key : ∀ k k' : H, (k : H ⧸ S) = k' → ρ k x = ρ k' x := by
    intro k k' h
    have h2 : ρ (k⁻¹ * k') x = x := QuotientGroup.eq.mp h
    calc ρ k x = ρ k (ρ (k⁻¹ * k') x) := by rw [h2]
      _ = ρ k' x := by rw [← hmul]; simp
  refine ⟨Finset.univ.image (fun q : H ⧸ S => (Quotient.out q : H)),
    ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ((1 : H) : H ⧸ S))⟩, ?_⟩
  intro h
  have hinj : Function.Injective (fun q : H ⧸ S => (Quotient.out q : H)) :=
    fun a b hab => Quotient.out_injective hab

  rw [Finset.sum_image hinj.injOn, map_sum]
  refine Fintype.sum_equiv (ι := H ⧸ S) (κ := H ⧸ S) (MulAction.toPerm h) _ _ ?_
  intro q
  show ρ h (ρ (Quotient.out q) x) = ρ (Quotient.out (h • q)) x
  rw [← hmul]
  apply key
  rw [QuotientGroup.out_eq']
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rfl
