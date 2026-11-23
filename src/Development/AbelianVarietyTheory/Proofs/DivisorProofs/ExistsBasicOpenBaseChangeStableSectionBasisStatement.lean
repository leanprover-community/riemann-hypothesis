module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBaseChangeStableSectionBasis
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out


theorem _root_.GlobalTheory.T.exists_basicOpen_baseChangeStable_sectionBasis : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.Rigidified A L → Out.RelAmple A L → ∀ k : ℕ, 1 ≤ k → ∀ p : Sp Rg, ∃ f : Rg, p ∈ PrimeSpectrum.basicOpen f ∧ ∀ g : Rg, PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f → ∀ (Ag : Over (Sp (Localization.Away g))) [GrpObj Ag] [IsCommMonObj Ag] (φ : Ag.left ⟶ A.left), IsGrpPullback Ag A (spMap (algebraMap Rg (Localization.Away g))) φ → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (overRes (T := baseOver (Sp (Localization.Away g))) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp (Localization.Away g))) ⊤).left) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (baseAt t))), (∀ i, IsPullSec Ag (L.pull φ) (k : ℤ) (homAt t ▷ Ag) (whiskerRight_snd (homAt t) Ag) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) = ⊤) := by
  first | exact @GlobalTheory.HomFixLocBasis.exists_basicOpen_secBasis | exact GlobalTheory.HomFixLocBasis.exists_basicOpen_secBasis | (intros; apply GlobalTheory.HomFixLocBasis.exists_basicOpen_secBasis <;> assumption)
