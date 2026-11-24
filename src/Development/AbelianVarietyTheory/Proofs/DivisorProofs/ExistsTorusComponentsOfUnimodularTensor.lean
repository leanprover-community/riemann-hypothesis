module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGtOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTorusPointOfComponentTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceMul
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_onto (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F) (hT : TensFacts W φ e wv)
    (hdet : IsUnit (W + W.transpose).det) (v' : N'.Gt) : ∃ vs : Fin r → N.Gt, GtRelV W φ e wv v' vs :=
  Vonto.of_exist_mul hT hdet (VExist.gtRelV_exists F N N' W φ e wv hT)
    (gtRelV_mul F N N' W φ e wv hT) v'

end GlobalTheory.Mum.TensTor
