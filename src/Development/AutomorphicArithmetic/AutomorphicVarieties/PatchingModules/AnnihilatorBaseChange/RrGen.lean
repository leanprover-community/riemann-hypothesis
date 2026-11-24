module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UGenApprox
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.RrExt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.rrGen :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A), GenBy O ({b | ∃ i g, b = W.t.D.lam i (MonoidAlgebra.single g 1)} ∪ {b | ∃ v i g, b = ((W.t.ψ v i g : W.Rˣ) : W.R)} ∪ {b | ∃ j i, b = W.t.U j i ∨ b = W.t.y j i} ∪ {W.t.s}) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W N x
  refine UpperTheory.V.CA.u_gen O W.R _ (fun R' _ _ _ f f' h => ?_) N x
  refine UpperTheory.V.Pa.Core.rrExt l L G0 T Λ n O r B u J D A W R' f f' (fun i g => h _ ?_) (fun v i g => h _ ?_)
    (h _ ?_) (fun j i => h _ ?_) (fun j i => h _ ?_)
  · exact .inl (.inl (.inl ⟨i, g, rfl⟩))
  · exact .inl (.inl (.inr ⟨v, i, g, rfl⟩))
  · exact .inr rfl
  · exact .inl (.inr ⟨j, i, .inl rfl⟩)
  · exact .inl (.inr ⟨j, i, .inr rfl⟩)
