module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThmUOfAllSet
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVarietyStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataUniformisationOfTorsionCouStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionEqOfLawsStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZH

theorem thmU_and_uTors : GlobalTheory.ZH.ThmUSt ∧ GlobalTheory.ZH.UTorsSt := by
  obtain ⟨L, L2, L3, L4, L5, -⟩ := GlobalTheory.T.all_six_abelian_scheme_laws_hold
  refine ⟨GlobalTheory.ZH.thmU_of_allSet L GlobalTheory.homExtension_semiAbelian_dvr (by
    have h := GlobalTheory.T.exists_degenerationData_uniformisation_of_torsionCount (GlobalTheory.T.card_torsion_points_abelianVariety L.globalFns L.rigidity) L L2
    intro V _ _ _ A G _ _ s
    obtain ⟨D, U, -, hg, -⟩ := h V A G s
    exact ⟨D, U, hg⟩), GlobalTheory.T.uniformisation_torsion_eq_of_laws L L2 L3 L4 L5⟩

end GlobalTheory.ZH
