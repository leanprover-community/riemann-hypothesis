module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalCoordinatesExtendProjectiveSpace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.CoverNorm

theorem unitAt_fnMap_of {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (g : Z ⟶ X)
    (hη : g (genericPoint Z) ⤳ genericPoint X) {x : Z} {t : X.functionField} (h : UnitAt (g x) t) :
    UnitAt x (SmallSec.fnMap g hη t) := by
  have h0 : t ≠ 0 := h.ne_zero
  rw [unitAt_iff ((map_ne_zero _).2 h0), ← map_inv₀]
  exact ⟨ProjSpace.regAt_fnMap_of g hη h.regAt, ProjSpace.regAt_fnMap_of g hη h.inv.regAt⟩

end GlobalTheory.CoverNorm
