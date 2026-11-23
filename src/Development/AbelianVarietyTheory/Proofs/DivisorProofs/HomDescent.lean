module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtalePointOfExt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActDescendOfGenerators
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgClosedDescent

theorem hom_descent : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B B' : Over (Sp k₀)) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → ∀ f : (Over.pullback (spMap (algebraMap k₀ K))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ K))).obj B', IsMonHom f → ∃! f₀ : B ⟶ B', IsMonHom f₀ ∧ (Over.pullback (spMap (algebraMap k₀ K))).map f₀ = f := by
  intro k₀ K _ _ _ _ B B' _ _ hB hB' f hf
  have hP : IsAbelianScheme (B ⊗ B') := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB hB'
  let i : B ⟶ B ⊗ B' := lift (𝟙 B) 1
  let j : B' ⟶ B ⊗ B' := lift 1 (𝟙 B')
  have hi : IsMonHom i := by
    have : IsMonHom (1 : B ⟶ B') := by
      rw [Hom.one_def]; infer_instance
    infer_instance
  have hj : IsMonHom j := by
    have : IsMonHom (1 : B' ⟶ B) := by
      rw [Hom.one_def]; infer_instance
    infer_instance
  obtain ⟨F₀, ⟨hF₀, hF⟩, -⟩ := endo_descent (K := K) (B ⊗ B') hP
    ((Over.pullback (spMap (algebraMap k₀ K))).map (fst B B') ≫ f ≫
      (Over.pullback (spMap (algebraMap k₀ K))).map j) inferInstance
  have key : (Over.pullback (spMap (algebraMap k₀ K))).map (i ≫ F₀ ≫ snd B B') = f := by
    rw [Functor.map_comp, Functor.map_comp, hF]
    simp only [Category.assoc]
    rw [← Functor.map_comp, ← Functor.map_comp_assoc, lift_fst, lift_snd,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id]
  exact ⟨i ≫ F₀ ≫ snd B B', ⟨inferInstance, key⟩, fun f₁ hf₁ =>
    ActDescent.pullback_map_injective (spMap (algebraMap k₀ K)) B B' (hf₁.2.trans key.symm)⟩

end GlobalTheory.AlgClosedDescent
