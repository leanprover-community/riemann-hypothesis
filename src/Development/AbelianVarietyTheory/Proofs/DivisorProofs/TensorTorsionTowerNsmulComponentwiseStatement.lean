module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionTowerNsmulComponentwise
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


theorem _root_.GlobalTheory.T.tensor_torsion_tower_nsmul_componentwise : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (n m : ℕ), 0 < n → 0 < m → ∀ (p' : QkPt D'.toPre F (n * m)) (ps : Fin r → QkPt D.toPre F (n * m)) (t' : QkPt D'.toPre F n) (ts : Fin r → QkPt D.toPre F n), PtRel T ν ν' p' ps → PtRel T ν ν' t' ts → (∀ i, ∃ q : QkPt D.toPre F n, q.y = (ps i).y ∧ GtPtF.IsNsmul m (ps i).g q.g ∧ QkPt.Equiv D.toPre F q (ts i)) → ∃ q' : QkPt D'.toPre F n, q'.y = p'.y ∧ GtPtF.IsNsmul m p'.g q'.g ∧ QkPt.Equiv D'.toPre F q' t' := by
  first | exact @GlobalTheory.Mum.TensTower.tower | exact GlobalTheory.Mum.TensTower.tower | (intros; apply GlobalTheory.Mum.TensTower.tower <;> assumption)
