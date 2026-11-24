module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingsFormsExistList
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithAtProperty
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedTiesStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEHasGridFldStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.LiteralAutomorphy
theorem rowGeo_at_gridA_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (CF : ℝ) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP),
    (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c →
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL CF K B f T w Z Wt p0 t nch n xd c)) →
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ) _root_.GlobalTheory.Fc.R1.SlotDivisorCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ) _root_.GlobalTheory.Fc.RL.Row_tie_alt →
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ) fun Q L => _root_.GlobalTheory.Fc.RL.RowGeometricCondition Q L CF := by
  intro hR hL CF N S Γ hN hD hT
  have hA := _root_.GlobalTheory.T.class_sum_divisor_all_alt hR hL (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ
    (fun K B f T w Z Wt p0 t nch n xd c h => (hN K B f T w Z Wt p0 t nch n xd c h.1).map fun x => x.1) hD
  have hG : _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ) fun S L => Row S L (AtAll fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) =>
      ∀ t : b.Comparison₂, (b.part t).pt.CompatibilityConditions → GlobalTheory.BigTop.Fun.HasGrid @GlobalTheory.BigTop.Fun.Fld (b.part t).pt CF) :=
    _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (RowE.row (_root_.GlobalTheory.T.grid_field_has_lattices_alt hL CF N S Γ hN))
  obtain ⟨R, r, h⟩ := RowL.and (RowL.and hA hG) hT
  refine ⟨R, r, Row.imp h fun 𝒜 σ _ H => ?_⟩
  intro eps Fm hc x hx i
  obtain ⟨t⟩ := H.2 Fm hc x hx i
  obtain ⟨a, b, c, d, e⟩ := H.1.1 Fm hc x hx i t
  exact ⟨t, a, b, c, d, e, H.1.2 Fm hc x hx i t c⟩
end GlobalTheory.Mem.LiteralAutomorphy
end
