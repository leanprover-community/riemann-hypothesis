module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
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

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ModelFn

open SmallSec

theorem ratVal_eq {Z : Scheme.{0}} [IsIntegral Z] {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ}
    (y : CxPts q σ) (f : Z.functionField) : ratVal f y = valAt y.1 f := by
  by_cases hf : RegAt (under y) f
  · exact ratVal_eq_valAt y hf
  · rw [ratVal, valAt, dite_eq_right hf, dite_eq_right hf]

theorem valAt_comp {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X) [IsPreimmersion j]
    (hη : j (genericPoint Y) ⤳ genericPoint X) {K : Type} [Field K] (y : Sp K ⟶ Y) (f : X.functionField) :
    valAt (y ≫ j) f = valAt y (fnMap j hη f) := by
  by_cases hf : RegAt (j (below y)) f
  · exact (valAt_fnMap j hη y hf).symm
  · have h₁ : ¬ RegAt (below (y ≫ j)) f := hf
    rw [valAt, valAt, dite_eq_right h₁, dite_eq_right (mt (regAt_fnMap_iff j hη).1 hf)]

end GlobalTheory.TrueGeo.ModelFn
