module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPolarisationBundlesCorrespondDeforma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_polarisation_bundles_correspond_deformations : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (s₁ s₂ : Sp (DualNumber k) ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (m₁ : GlobalTheory.UPel.HT.ObjMap o₀ o₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (m₂ : GlobalTheory.UPel.HT.ObjMap o₀ o₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (e : o₁.A ≅ o₂.A), IsMonHom e.hom → m₁.φ ≫ e.hom.left = m₂.φ → ∀ φ₂ : (G2 o₁.A).left ⟶ (G2 o₂.A).left, IsSquare e.hom.left φ₂ → LBIso o₁.P (o₂.P.pull φ₂) := by
  first | (exact @GlobalTheory.UPel.HT.PolIsoLift.pol_iso) | (exact GlobalTheory.UPel.HT.PolIsoLift.pol_iso) | (intros; apply GlobalTheory.UPel.HT.PolIsoLift.pol_iso  <;> assumption)
