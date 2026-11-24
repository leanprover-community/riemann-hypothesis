module

public import Formalism.AlgebraicWeights.IsAlgWeight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TSetFinLoc

open GlobalTheory.TSetFin

theorem finite_image_tSet_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ J : Subgroup (GAf L n),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) → ∀ k : ℕ,
    ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' tSet L n s ϖ k).Finite := by
  intro L _ _ _ n s ϖ hϖ J hJ k
  classical
  obtain ⟨c, hc⟩ := approx_class s.v
  haveI : Finite (𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ s.v.ne_bot
  let κ : GAf L n → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := fun x =>
    if h : x ∈ tSet L n s ϖ k then
      fun i j => c (((h.2.choose : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j)
    else 0
  have key : ∀ x ∈ tSet L n s ϖ k, ∀ x' ∈ tSet L n s ϖ k, κ x = κ x' →
      (x : GAf L n ⧸ J) = x' := by
    intro x hx x' hx' hκ
    simp only [κ, dif_pos hx, dif_pos hx'] at hκ
    obtain ⟨ha, b, hb, hg⟩ := hx.2.choose_spec
    obtain ⟨ha', b', hb', hg'⟩ := hx'.2.choose_spec
    set a := hx.2.choose
    set a' := hx'.2.choose
    have ia := glint_int ha
    have ia' := glint_int ha'
    have ib := glint_int hb
    have ib' := glint_int hb'
    have hcl : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j -
        (a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1 := fun i j =>
      hc _ _ (ia.1 i j) (ia'.1 i j) (congrFun (congrFun hκ i) j)
    have hcl' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j -
        (a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1 := fun i j => by
      rw [← Valuation.map_neg, neg_sub]; exact hcl i j
    have hunif : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
    have h1 := local_int s.v ϖ k hunif a a' b b' _ _ ia'.1 ia.2 ib.2 ib'.1 hcl hg hg'
    have h2 := local_int s.v ϖ k hunif a' a b' b _ _ ia.1 ia'.2 ib'.2 ib.1 hcl' hg' hg
    rw [QuotientGroup.eq]
    have htriv : TrivOutside {s.v} (x⁻¹ * x') := triv_mul (triv_inv hx.1) hx'.1
    refine (hJ _ htriv).2 ?_
    exact mem_Umax_of_loc s _ htriv (fun i j => by
      rw [map_mul, map_inv]; exact h1 i j) (fun i j => by
      rw [mul_inv_rev, inv_inv, map_mul, map_inv]; exact h2 i j)
  let g : GAf L n ⧸ J → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := fun q =>
    if h : ∃ x ∈ tSet L n s ϖ k, (x : GAf L n ⧸ J) = q then κ h.choose else 0
  refine Set.Finite.of_finite_image (f := g) (Set.toFinite _) ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ hgg
  have h : ∃ y ∈ tSet L n s ϖ k, (y : GAf L n ⧸ J) = x := ⟨x, hx, rfl⟩
  have h' : ∃ y ∈ tSet L n s ϖ k, (y : GAf L n ⧸ J) = x' := ⟨x', hx', rfl⟩
  simp only [g, dif_pos h, dif_pos h'] at hgg
  show (x : GAf L n ⧸ J) = x'
  rw [← h.choose_spec.2, ← h'.choose_spec.2]
  exact key _ h.choose_spec.1 _ h'.choose_spec.1 hgg

end GlobalTheory.TSetFinLoc

end
