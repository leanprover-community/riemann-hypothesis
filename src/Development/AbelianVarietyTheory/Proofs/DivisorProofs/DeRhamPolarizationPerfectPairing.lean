module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamFreeHodgeSequenceBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationOrthogonalPerfectStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerfPairDualOfHalfDimKernelConditionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationOfOrthogonalPerfectPairingStatement
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
import Mathlib.Tactic.TypeStar

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FieldPerf

theorem finrank_of_rankAtStalk {k : Type} [Field k] {M : Type*} [AddCommGroup M] [Module k M]
    [Module.Finite k M] {n : ℕ} (h : ∀ p : PrimeSpectrum k, Module.rankAtStalk M p = n) :
    Module.finrank k M = n := by
  have e := h ⟨⊥, Ideal.isPrime_bot⟩
  rwa [Module.rankAtStalk_eq_finrank_of_free] at e

theorem isPerfPair : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[k] HdR B →ₗ[k] k, AbDual.IsCorrForm (dp0 k) (𝟙 _) A B P φ → φ.IsPerfPair := by
  intro H k _ A B _ _ g hA hB gA gB P hP φ hφ
  obtain ⟨HF, HH, -⟩ := GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange H
  obtain ⟨fA, -, rA⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim HF hA gA
  obtain ⟨fB, -, rB⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim HF hB gB
  obtain ⟨-, -, fFA, -, rFA⟩ := HH k A g hA gA
  obtain ⟨-, -, fFB, -, rFB⟩ := HH k B g hB gB
  exact GlobalTheory.T.isPerfPair_dual_of_half_dim_kernel_conditions k (primDR A) (primDR B) (PrimitiveSubmodule A) (PrimitiveSubmodule B) g
    (finrank_of_rankAtStalk rA) (finrank_of_rankAtStalk rB)
    (finrank_of_rankAtStalk rFA) (finrank_of_rankAtStalk rFB) φ
    (GlobalTheory.T.hodge_filtration_orthogonal_perfect H k A B g hA hB gA gB P hP φ hφ)
    (GlobalTheory.T.mem_hodgeFiltration_of_orthogonal_perfectPairing H k A B g hA hB gA gB P hP φ hφ)

end GlobalTheory.FieldPerf
