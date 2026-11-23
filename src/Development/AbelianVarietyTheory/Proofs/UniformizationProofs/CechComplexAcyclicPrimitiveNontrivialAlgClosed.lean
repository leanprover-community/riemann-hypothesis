module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankCechLBHomologyExtProd
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFinAffineCover
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
namespace GlobalTheory.PrimVan

theorem cechLB_acyclic_of_primitive :
    ∀ (K : Type) [Field K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B],
      IsAbelianScheme B → IsProjBy B.hom → ∀ M : LB B.left, M.IsLB →
      (∃ u : LB.Gen (abelian₂ B M), u.IsGen) → ¬ Triv M →
      ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → B.left.Opens), (∀ i, IsAffineOpen (D i)) →
        ⨆ i, D i = ⊤ → ∀ n, (cechLB B.hom M D).ExactAt n ∧ IsZero ((cechLB B.hom M D).homology n) ∧
          Module.finrank K ((cechLB B.hom M D).homology n) = 0 := by
  intro K _ B _ _ hB hP M hM hu hn κ _ _ D hD hc n
  have := hB.proper
  have h := acyclic_of_kuenneth GlobalTheory.AbLaw.finrank_cechLB_homology_extProd hB hM (lbIso_pull_mul hM hu) (subsingleton_sec hB hM hu hn)
    hD hc (GlobalTheory.AbLaw.cechLB_homology_finite_of_affine_cover K _ _ M κ D hM inferInstance hP hD hc)
    (GlobalTheory.AbLaw.cechLB_homology_finite_of_affine_cover K _ _ _ κ D (Inh.trivLB_isLB _) inferInstance hP hD hc) n
  have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 h
  have := ModuleCat.isZero_iff_subsingleton.1 hz
  exact ⟨h, hz, Module.finrank_zero_of_subsingleton⟩

theorem acyclic_cechLB_of_primitive :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ M : LB B.left, M.IsLB → (∃ u : LB.Gen (abelian₂ B M), u.IsGen) → ¬ Triv M → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (B.left).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (B.hom) (M) D).Acyclic) :=
  fun K _ _ B _ _ hB hP M hM hu hn κ _ _ D hD hc n =>
    (cechLB_acyclic_of_primitive K B hB hP M hM hu hn κ D hD hc n).1

end GlobalTheory.PrimVan
