module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarriedOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmEqMapGm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFrameOfSectionUnitsOnClosedFibre
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_lineBundleFrame_of_section_units_on_closedFibre : ∀ (X Y : Scheme.{0}) (β : X ⟶ Y), IsClosedMap β.base → ∀ (L : LB X), L.IsLB → ∀ (V : Y.Opens) (s : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V ⊓ L.U k)), IsSecOver L (β ⁻¹ᵁ V) s → ∀ y : Y, y ∈ V → (∀ (z : X) (k : L.ι), β z = y → z ∈ L.U k → IsUnit (gs (𝟙 X) z (β ⁻¹ᵁ V ⊓ L.U k) (s k))) → ∃ V' : Y.Opens, y ∈ V' ∧ V' ≤ V ∧ ∃ T : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V' ⊓ L.U k)ˣ, IsFrameOver L (β ⁻¹ᵁ V') T ∧ ∀ (f : X ⟶ X) (w : LB.Iso L (L.pull f)), SecCarriedOver L (β ⁻¹ᵁ V) s f w → FrameCarried L (β ⁻¹ᵁ V') T f w := by
  first | exact @GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre | exact GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre | (intros; apply GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre <;> assumption)
