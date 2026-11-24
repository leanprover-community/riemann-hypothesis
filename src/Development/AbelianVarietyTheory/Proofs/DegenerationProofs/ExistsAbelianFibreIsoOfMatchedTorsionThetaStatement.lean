module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAbelianFibreIsoOfMatchedTorsionTheta
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
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

theorem _root_.GlobalTheory.T.exists_abelianFibre_iso_of_matched_torsion_theta : Laws → ThetaPtDeterminesSt → BrUthSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R), D.PsiEven → D.TauBimult → D'.PsiEven → D'.TauBimult → D.P.g = D'.P.g → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (Q Q' : PolAV (Sp F)) (Φ : Q.A.left ⟶ D.P.A.left) (Φ' : Q'.A.left ⟶ D'.P.A.left), IsFib D F Q Φ → IsFib D' F Q' Φ' → ∀ n : ℕ, n.Prime → Odd n → (n : F) ≠ 0 → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (c : F) (ρ : N.A → N'.A), c ≠ 0 → TorsMap N.toNumB N'.toNumB (n ^ j) c ρ → ∃ σ : Q.A ≅ Q'.A, IsPolIso Q Q' σ ∧ ∀ (x : baseOver (Sp F) ⟶ Q.A) (b : N.A), b ^ (n ^ j) ^ 2 = 1 → (ν.eA b).left = x.left ≫ Φ → (ν'.eA (ρ b)).left = (x ≫ σ.hom).left ≫ Φ' := by
  first | exact @GlobalTheory.Ex.FibIso.exists_iso_fib | exact GlobalTheory.Ex.FibIso.exists_iso_fib | (intros; apply GlobalTheory.Ex.FibIso.exists_iso_fib <;> assumption)
