module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8LB
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8CubicalEvenPolarizationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerPolarizedGenericFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreUniformisationEvenTorusCompleteNormalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisedFibrewiseNonvanishingSectionStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

theorem thetaNZ_e8LB : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → GlobalTheory.LN.ThetaNZ (powObj G₀ 8) (GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W) := by
  intro hL hL2 hE V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ hS W hW
  have hB : GlobalTheory.Mum.Base V₁ := by
    obtain ⟨h1, h2, h3, h4⟩ := hCN
    exact ⟨⟨h1, inferInstance, h2, h3⟩, h4⟩
  obtain ⟨Pc, hPc, hEv⟩ := GlobalTheory.T.exists_cubical_e8LB_evenOn hL hL2 hE V₁ hCN D₀ G₀ A₀ U₀ hS W hW
  obtain ⟨A, gen, hgen, hA⟩ := GlobalTheory.T.exists_polAV_generic_fibre_e8LB hL hL2 hE V₁ hCN D₀ G₀ A₀ U₀ hS W hW
  have hS8 : IsSemiAbelian (powObj G₀ 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS
  obtain ⟨D, U, hU, -⟩ := GlobalTheory.T.exists_preUniformisation_even_torus_completeNormal V₁ hB _ Pc hS8 hEv A gen hgen (hPc ▸ hA)
  have h := GlobalTheory.T.preUniformised_fibrewise_nonvanishing_section V₁ hB D A _ U (hU ▸ hEv)
  rw [hU, hPc] at h
  exact h

end GlobalTheory.PowE8
end
