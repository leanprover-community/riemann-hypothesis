module

public import Formalism.ConjugateSelfDual.Statement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingPadicAlgClPlace
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
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.adicNorm_prod_le_prod_of_injective_classes :
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (O S R : Type) [Fintype O] [Fintype S] (f : O → S → ℂ), (∀ o s, IsIntegral ℤ (f o s)) → ∀ (X : O → Finset R) (cl : ∀ o, ↥(X o) → S), (∀ o, Function.Injective (cl o)) → ‖ι.symm (∏ o, ∏ s, f o s)‖ ≤ ∏ o, ∏ r : ↥(X o), ‖ι.symm (f o (cl o r))‖ := by
  intro l _ ι O S R _ _ f hf X cl hcl
  classical
  have h1 : ∀ o s, ‖ι.symm (f o s)‖ ≤ 1 := fun o s =>
    GlobalTheory.norm_le_one_of_isIntegral_int (map_isIntegral_int ι.symm (hf o s))
  rw [map_prod, norm_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun o _ => ?_)
  rw [map_prod, norm_prod]
  have h2 : ∏ r : ↥(X o), ‖ι.symm (f o (cl o r))‖
      = ∏ s ∈ Finset.univ.map ⟨cl o, hcl o⟩, ‖ι.symm (f o s)‖ := by
    rw [Finset.prod_map]; rfl
  rw [h2]
  exact Finset.prod_le_prod_of_subset_of_le_one₀ (Finset.subset_univ _)
    (fun _ _ => norm_nonneg _) (fun s _ _ => h1 o s)
