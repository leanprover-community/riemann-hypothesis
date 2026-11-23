module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_iso_of_compatible_abelianThickenings : SecBaseChangeSt → AmpleSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P P' : PolAV (Spec (CommRingCat.of R))) (β : ∀ e : ℕ, thickObj R I e P'.A ≅ thickObj R I e P.A) (v : ∀ e : ℕ, LB.Iso (P'.L.pull (fstG I e P'.A).left) (P.L.pull ((β e).hom.left ≫ (fstG I e P.A).left))), (∀ e, (v e).IsGen) → (∀ e, thickMap R I e P'.A ≫ (β (e + 1)).hom.left = (β e).hom.left ≫ thickMap R I e P.A) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι), (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' → Geo.Tor.gw (v (e + 1)) (r ≫ thickMap R I e P'.A) z j (fun _ => j') = Geo.Tor.gw (v e) r z j (fun _ => j')) → ∃ (Φ : P'.A ≅ P.A) (w : LB.Iso P'.L (P.L.pull Φ.hom.left)), w.IsGen ∧ ∀ e : ℕ, (fstG I e P'.A).left ≫ Φ.hom.left = (β e).hom.left ≫ (fstG I e P.A).left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι), (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' → Geo.Tor.gw w (r ≫ (fstG I e P'.A).left) z j j' = Geo.Tor.gw (v e) r z j (fun _ => j') := by
  first | exact @GlobalTheory.exists_iso_of_compatible_thickenings | exact GlobalTheory.exists_iso_of_compatible_thickenings | (intros; apply GlobalTheory.exists_iso_of_compatible_thickenings <;> assumption)
