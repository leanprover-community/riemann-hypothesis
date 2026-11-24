module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.ipEq :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n), (∀ u, (residOf r).Ip u = r.Ip u ∧ (residOf r).Ip u = (globOf r V0).frame.Iu u) ∧ ∀ [IsNoetherianRing O] (B : UniversalOrdinaryDeterminantRing r), augmentationIdealKernel (pairOf B.u) = {z | z ∈ B.GroupAlgebraKernelIdeal} := by
  intro l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ n r
  have h1 : ∀ u, (residOf r).Ip u = r.Ip u := by
    intro u
    refine le_antisymm (residOf_Ip_le r u) ?_
    rintro g ⟨⟨γ, hγ, rfl⟩, h2⟩
    refine ⟨⟨⟨γ, Ine_le_Dec _ hγ⟩, ⟨hγ, ?_⟩, rfl⟩, h2⟩
    exact Subgroup.mem_iInf.2 fun i => Subgroup.mem_iInf.1 h2 i
  have h2 : ∀ u, (residOf r).Ip u = (globOf r V0).frame.Iu u := by
    intro u
    refine le_antisymm inf_le_left (le_inf le_rfl ?_)
    rintro g ⟨γ, ⟨-, h⟩, rfl⟩
    exact Subgroup.mem_iInf.2 fun i => Subgroup.mem_iInf.1 h i
  refine ⟨fun u => ⟨h1 u, h2 u⟩, ?_⟩
  intro _ B
  have h3 : (pairOf B.u).D.CH ∪ pairGens (pairOf B.u) = B.E0gens := by
    unfold pairGens UniversalOrdinaryDeterminantRing.E0gens
    simp only [h1]
    rw [Set.union_assoc]
    rfl
  have h4 : (pairOf B.u).D.chBar (pairGens (pairOf B.u)) = B.GroupAlgebraKernelIdeal :=
    congrArg (closureIdeal (maximalIdeal B.B)) h3
  exact congrArg (fun K : TwoSidedIdeal (MonoidAlgebra B.B V0.frame.G₀) => {z | z ∈ K}) h4
