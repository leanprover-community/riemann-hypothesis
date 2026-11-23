module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcTorsionLabelsActionCompat
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

theorem _root_.GlobalTheory.T.arcTorsionLabels_action_compat : Laws → BrGtSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [NormedField C] [IsAlgClosed C] [Algebra (FractionRing R) C] (A : ArcF D R C) (o : Full D C) (M : Mdl o), M.P.TorsionIso → ∀ (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (k : ℕ) (β : A.N.Form k) (u r : Cˣ) (J : NumD.Iso (A.N.twist β u) N') (j : ℕ), 0 < j → r ^ j = u → (∀ x (p : (A.N.twist β u).QT j) (q' : N'.QT j) p' z, TwRel β u r (A.q _ x) p → q'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 q'.1.2 → ν'.QPt p' q' → z.left = (o.I.ev j x).left ≫ M.φ → M.P.ToA C j p' z) → ∀ (x : 𝓞 E) (b : A.N.A), b ^ j = 1 → J.φ (actV (N := A.N) A.ν A.oa.onB x b) = actV ν' M.P.oD.onB x (J.φ b) := by
  first | exact @GlobalTheory.Relabel.act_compat_on_torsion | exact GlobalTheory.Relabel.act_compat_on_torsion | (intros; apply GlobalTheory.Relabel.act_compat_on_torsion <;> assumption)
