module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsUnitEv
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusWeightTestGenericPointRationalPoints
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.splitTorusWeight_test_genericPoint_rationalPoints : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], Smooth G.hom → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G) (F : Type) [Field F] (s : Sp F ⟶ Sp k) (g : Over.mk s ⟶ G), (∀ V : G.left.Opens, (V : Set G.left).Nonempty → ⊤ ≤ g.left ⁻¹ᵁ V) → ∀ (V : G.left.Opens) (u : Γ(G.left, V)) (χ : X), (∀ (t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) (h₁ : ⊤ ≤ (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V), WtRat.ev (R := F) (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left V h₁ u = WtRat.ev (R := F) (toUnit (Over.mk s) ≫ t).left ⊤ le_top (charUnit (Sp k) X χ).val * WtRat.ev (R := F) g.left V h₂ u) → Wt i V u χ := by
  first | exact @GlobalTheory.SS.WtRat.wt_of_genericPoint | exact GlobalTheory.SS.WtRat.wt_of_genericPoint | (intros; apply GlobalTheory.SS.WtRat.wt_of_genericPoint <;> assumption)
