module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


namespace GlobalTheory.ParIndExact

theorem parInd_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (ξ : Representation ℂ (Levi k m) X) (η : Representation ℂ (Levi k m) Y) (i : ξ.IntertwiningMap η), Function.Injective i → Function.Injective (parIndMap e i) ∧ ∀ (Z : Type) [AddCommGroup Z] [Module ℂ Z] (ζ : Representation ℂ (Levi k m) Z) (q : η.IntertwiningMap ζ), (∀ y, q y = 0 → ∃ x, i x = y) → ∀ φ, parIndMap e q φ = 0 → ∃ ψ, parIndMap e i ψ = φ := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e X Y _ _ _ _ ξ η i hi
  have hval : ∀ (φ : IndSp e ξ) (g : GL n k), (parIndMap e i φ).1.1 g = i (φ.1.1 g) := fun _ _ => rfl
  refine ⟨?_, ?_⟩
  · intro φ ψ hφψ
    refine Subtype.ext (Subtype.ext (funext fun g => hi ?_))
    rw [← hval, ← hval, hφψ]
  · intro Z _ _ ζ q hex φ hφ
    have h0 : ∀ g, q (φ.1.1 g) = 0 := fun g =>
      congrFun (congrArg (fun χ : IndSp e ζ => χ.1.1) hφ) g
    choose x hx using fun g => hex _ (h0 g)
    have hlaw : x ∈ indSpace (parab k e) ((twist ξ (deltaHalf k m)).comp (leviProj k e)) := by
      intro p g
      apply hi
      rw [hx]
      have h1 := parInd_law e η φ p g
      rw [h1, ← hx g]
      show _ = i ((deltaHalf k m (leviProj k e p) : ℂ) • ξ (leviProj k e p) (x g))
      rw [map_smul, i.isIntertwining]
    let x' : indSpace (parab k e) ((twist ξ (deltaHalf k m)).comp (leviProj k e)) := ⟨x, hlaw⟩
    have hset : {g : GL n k | ind (parab k e) ((twist ξ (deltaHalf k m)).comp (leviProj k e)) g x' = x'} =
        {g : GL n k | ind (parab k e) ((twist η (deltaHalf k m)).comp (leviProj k e)) g φ.1 = φ.1} := by
      ext g
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        apply Subtype.ext
        funext y
        have hy := congrFun (congrArg Subtype.val h) y
        change x (y * g) = x y at hy
        change φ.1.1 (y * g) = φ.1.1 y
        rw [← hx, ← hx, hy]
      · intro h
        apply Subtype.ext
        funext y
        have hy := congrFun (congrArg Subtype.val h) y
        change φ.1.1 (y * g) = φ.1.1 y at hy
        change x (y * g) = x y
        apply hi
        rw [hx, hx, hy]
    have hsm : x' ∈ smoothPart (ind (parab k e) ((twist ξ (deltaHalf k m)).comp (leviProj k e))) := by
      have ho : IsOpen {g : GL n k | ind (parab k e) ((twist ξ (deltaHalf k m)).comp (leviProj k e)) g x' = x'} := by
        rw [hset]; exact φ.2
      exact ho
    refine ⟨⟨x', hsm⟩, ?_⟩
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    rw [hval]
    exact hx g

end GlobalTheory.ParIndExact
