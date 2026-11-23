module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuesIsoRespectsEndomorphismOfTorsionCompat
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

theorem _root_.GlobalTheory.T.valuesIso_respects_endomorphism_of_torsion_compat : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (I : NumB.Iso N.toNumB N'.toNumB), GeoIso ν ν' I → ∀ (O : Type) [CommRing O] [StarRing O] (oa : D.P.OAct O) (oa' : D'.P.OAct O) (n : ℕ), n.Prime → (n : F) ≠ 0 → ∀ x : O, (∀ (j : ℕ) (b : N.A), b ^ n ^ j = 1 → I.φ (actV ν oa x b) = actV ν' oa' x (I.φ b)) → ∀ b, I.φ (actV ν oa x b) = actV ν' oa' x (I.φ b) := by
  first | exact @GlobalTheory.Relabel.actV_compat_of_torsion | exact GlobalTheory.Relabel.actV_compat_of_torsion | (intros; apply GlobalTheory.Relabel.actV_compat_of_torsion <;> assumption)
