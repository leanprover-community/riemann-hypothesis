module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowerGaloisExtSymplecticLevel
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR


theorem _root_.GlobalTheory.T.exists_primePower_galois_ext_symplecticLevel : ∀ {Ω₁ : Type} [Field Ω₁] [CharZero Ω₁] {R₁ : Type} [CommRing R₁] (emb : R₁ →+* Ω₁) (P₁ : PolAV (Sp R₁)) (ℓ M K : ℕ), ℓ.Prime → 0 < M → ℓ ∣ M → (∃ e, K = ℓ ^ e) → (∃ ζ₀ : Ω₁, IsPrimitiveRoot ζ₀ M) → (∀ (E : Type) [Field E] [IsAlgClosed E] (x : Sp E ⟶ Sp R₁) (z : Over.mk x ⟶ P₁.A), z ^ M = 1 → ∃ y : baseOver (Sp R₁) ⟶ P₁.A, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R₁)) ≫ y = z) → ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra Ω₁ Ω₂) (Q : PolAV (Sp Ω₂)) (φ : Q.A.left ⟶ P₁.A.left) (ζ : Ω₂ˣ), FiniteDimensional Ω₁ Ω₂ ∧ IsGalois Ω₁ Ω₂ ∧ (∃ e, Module.finrank Ω₁ Ω₂ = ℓ ^ e) ∧ IsPrimitiveRoot ζ K ∧ Q.g = P₁.g ∧ IsGrpPullback Q.A P₁.A (spMap ((algebraMap Ω₁ Ω₂).comp emb)) φ ∧ LBIso Q.L (P₁.L.pull φ) ∧ Nonempty (Out.Level Q K (unitOn ζ)) := by
  first | exact @GlobalTheory.LevelPrimePower.exists_level_primePower | exact GlobalTheory.LevelPrimePower.exists_level_primePower | (intros; apply GlobalTheory.LevelPrimePower.exists_level_primePower <;> assumption)
