module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSectionsLocallyGenerated
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.ideal_sections_locally_generated : ∀ (X : Scheme.{0}) (M : LB X), M.IsLB → ∀ (I : X.IdealSheafData), IsGloballyGenerated (twist (idealModule I) M) → ∃ (n : ℕ) (σ : Fin n → M.Sec), (∀ (k : Fin n) (i : M.ι) (W : X.affineOpens) (h : W.1 ≤ M.U i), resG X h ((σ k).f i) ∈ I.ideal W) ∧ ∀ (x : X) (i : M.ι) (hx : x ∈ M.U i) (W : X.affineOpens) (hxW : x ∈ W.1) (a : Γ(X, W.1)), a ∈ I.ideal W → X.presheaf.germ W.1 x hxW a ∈ Ideal.span (Set.range fun k => X.presheaf.germ (M.U i) x hx ((σ k).f i)) := by
  first | exact @_root_.GlobalTheory.Twist.exists_secs_generating_ideal | exact _root_.GlobalTheory.Twist.exists_secs_generating_ideal | (intros; apply _root_.GlobalTheory.Twist.exists_secs_generating_ideal <;> assumption)
