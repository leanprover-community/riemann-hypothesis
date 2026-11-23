module

public import ReciprocityTheory.DualLattices.CotangentSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem htd_restrict_coefficients : ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe) (cp : R), HodgeTateSetting p v R Oe σ cp → ∀ H : HodgeTateDatum p g v R Oe σ cp, HodgeTateSetting p v R ℤ_[p] AlgEquiv.refl cp ∧ ∃ H' : HodgeTateDatum p g v R ℤ_[p] AlgEquiv.refl cp, H'.AA = H.AA ∧ H'.Ht = H.Ht ∧ H'.Bt = H.Bt ∧ H'.E = H.E := by
  intro p _ g C _ v R _ _ _ Oe _ _ σ cp hS H
  refine ⟨⟨hS.integers, hS.p_lt, hS.p_ne, hS.cp_val, fun _ => rfl⟩,
    { ρ := H.ρ.comp (Algebra.ofId _ _)
      ρL := H.ρL.comp (algebraMap _ _)
      P := H.P
      PL := H.PL
      E := H.E
      E_alternating := H.E_alternating
      isUnit_det_E := H.isUnit_det_E
      E_equivariant := fun a => ?_
      projectors := ⟨H.projectors.1, H.projectors.2.1, H.projectors.2.2.1, fun a => H.projectors.2.2.2.1 _, fun a => H.projectors.2.2.2.2 _⟩
      Ht := H.Ht
      Bt := H.Bt
      Ht_equivariant := ⟨fun a => ?_, H.Ht_equivariant.2⟩
      form_eq_alt := H.form_eq_alt
      AA := H.AA
      h3 := fun a => H.h3 _
      h4 := H.h4
      h5 := H.h5
      φ := H.φ
      cotangent_surjective := H.cotangent_surjective
      cotangent_ker_eq := H.cotangent_ker_eq
      cotangent_linear := fun a => H.cotangent_linear _ }, rfl, rfl, rfl, rfl⟩
  · have := H.E_equivariant (algebraMap ℤ_[p] Oe a)
    rw [σ.commutes] at this
    exact this
  · have := H.Ht_equivariant.1 (algebraMap ℤ_[p] Oe a)
    rw [σ.commutes] at this
    exact this

end GlobalTheory.CompanionTheory.Ar.GR
