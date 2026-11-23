module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivationDetEqUnitMulProdNormalCrossings
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.logDerivation_det_eq_unit_mul_prod_normalCrossings : ∀ (F A R : Type) [Field F] [CommRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] [IsNoetherianRing A] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] [Algebra.FiniteType F A] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (n m : ℕ) (x : Fin n → A) (e : Fin m ↪ Fin n) (J : Finset (Fin m)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m (fun j => algebraMap A R (x (e j))) → (∃ bs : Module.Basis (Fin n) R Ω[R⁄F], ∀ i, bs i = KaehlerDifferential.D F R (algebraMap A R (x i))) → ∀ (I : Ideal A), I.map (algebraMap A R) = Ideal.span {algebraMap A R (∏ j ∈ J, x (e j))} → ∀ (b : Fin n → Derivation ℤ A A), (∀ j c, b j (algebraMap F A c) = 0) → (∀ j, ∀ f ∈ I, b j f ∈ I) → (∀ D : Derivation ℤ A A, (∀ c, D (algebraMap F A c) = 0) → (∀ f ∈ I, D f ∈ I) → ∃ c : Fin n → A, D = ∑ j, c j • b j) → ∃ u : Rˣ, algebraMap A R (GlobalTheory.LogPole.logDet b x) = u * algebraMap A R (∏ j ∈ J, x (e j)) := by
  first | exact @GlobalTheory.logDet_local_eq_unit_mul_prod | exact GlobalTheory.logDet_local_eq_unit_mul_prod | (intros; apply GlobalTheory.logDet_local_eq_unit_mul_prod <;> assumption)
