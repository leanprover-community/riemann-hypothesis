module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointRepresentingWeightMumfordQuotientStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtMulAddStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtUniqueStatement
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem exists_weightPoints : Laws → AllSet fun s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∃ c : s.X → (𝟙_ _ ⟶ a.B), (∀ χ χ', c (χ + χ') = c χ * c χ') ∧ ∀ χ e, a.RepWt (c χ) χ e := by
  intro hL V _ _ _ A G _ _ s
  have h1 := GlobalTheory.T.exists_point_representing_weight_mumfordQuotient hL V A G s
  have h2 := GlobalTheory.T.mumfordTower_repWt_unique hL V A G s
  have h3 := GlobalTheory.T.mumfordTower_repWt_mul_add V A G s
  intro t a hK
  choose c hc using h1 t a hK
  refine ⟨c, fun χ χ' => ?_, hc⟩
  exact h2 t a hK (χ + χ') _ _ (hc _) fun e => h3 t a χ χ' _ _ e (hc χ e) (hc χ' e)

end GlobalTheory.UU
