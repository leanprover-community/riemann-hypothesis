module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpOfIsCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechClassPullHO1EqZeroOfPullbackCoboundary
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

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.cechClass_pullHO1_eq_zero_of_pullback_coboundary : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) [Z.IsSeparated] (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (Y : Scheme.{0}) (s' : Y ⟶ Sp R') (ι : Y ⟶ Z) (w : ι ≫ s = s' ≫ spMap σ) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c → (∃ h' : ∀ i, Γ(Y, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG Y inf_le_left (h' i) - resG Y inf_le_right (h' i')) → GlobalTheory.CechDR.pullHO1 w (GlobalTheory.CechCmp.cmp s W hW c) = 0 := by
  first | exact @GlobalTheory.CechCmp.pullHO1_cmp_eq_zero_of_coboundary | exact GlobalTheory.CechCmp.pullHO1_cmp_eq_zero_of_coboundary | (intros; apply GlobalTheory.CechCmp.pullHO1_cmp_eq_zero_of_coboundary <;> assumption)
