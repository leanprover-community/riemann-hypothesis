module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
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

@[expose] public section

open UpperTheory.V.Lit.Geo.Cs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr Filter Topology

theorem UpperTheory.V.Lit.Geo.Cs.locBd :
    LocBd := by
  intro E _ _ a p₀ hp
  obtain ⟨τ, h1, h2⟩ := locSec E a p₀ hp
  have c1 : ContinuousAt (fun p => toL (τ p).val) p₀ := h1.continuousAt
  have c1' : ContinuousAt (fun p => ((τ p).val : Matrix (Fin a) (Fin a) (Cinf E))) p₀ := c1
  have hi : ContinuousAt (Inv.inv : Matrix (Fin a) (Fin a) (Cinf E) → _) (τ p₀).val := by
    apply continuousAt_matrix_inv
    have := NormedRing.inverse_continuousAt (GeneralLinearGroup.det (τ p₀))
    simpa using this
  have c2' : ContinuousAt (fun p => (((τ p)⁻¹).val : Matrix (Fin a) (Fin a) (Cinf E))) p₀ := by
    have := ContinuousAt.comp (f := fun p => ((τ p).val : Matrix (Fin a) (Fin a) (Cinf E))) hi c1'
    simpa only [Matrix.coe_units_inv, Function.comp_def] using this
  have c2 : ContinuousAt (fun p => toL ((τ p)⁻¹).val) p₀ := c2'
  refine ⟨max (‖toL (τ p₀).val‖ + 1) (‖toL ((τ p₀)⁻¹).val‖ + 1), ?_⟩
  filter_upwards [h2, c1.norm.eventually_lt_const (lt_add_one _), c2.norm.eventually_lt_const (lt_add_one _)]
    with p e b1 b2
  exact ⟨τ p, ⟨b1.le.trans (le_max_left _ _), b2.le.trans (le_max_right _ _)⟩, e⟩
