module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteFreeNbhdStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullbackStructureModuleIso
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjFormulaTop

theorem topSelf_pull_eq_mul : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) [CharZero k] (D : ℕ), IsProjOver p → IsProjOver q → topologicalKrullDim X ≤ D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ B : LB X, B.IsLB → letI := GlobalTheory.algebraΓOfHom p; letI := GlobalTheory.algebraΓOfHom q; topSelfIntersection k (B.pull π) D = (π.residueDegree (genericPoint Y) : ℤ) * topSelfIntersection k B D := by
  intro k _ X Y _ _ p q _ D hp hq hD π hπ hgen hdeg B hB
  obtain ⟨U, hU, hgU, hU', -, hfin, hfree, hrank⟩ :=
    GlobalTheory.T.exists_affine_etale_finite_free_nbhd k X Y p q hp hq π hπ hgen hdeg
  subst hπ
  letI := GlobalTheory.algebraΓOfHom p
  letI := GlobalTheory.algebraΓOfHom (π ≫ p)
  rw [topSelf_def, topSelf_def]
  letI := (π.app U).hom.toAlgebra
  have hfin' : Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := hfin
  exact GlobalTheory.FieldProj.interNum_pull_eq_mul k Y X p π hq hp U _ hgU hU hU'
    ⟨hfree, hfin', hrank⟩ D hD (fun _ => B) (fun _ => hB)

end GlobalTheory.ProjFormulaTop
