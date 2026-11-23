module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpOfIsCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1ClassEqOfCocycleAffineCover
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

theorem _root_.GlobalTheory.T.cech_h1_class_eq_of_cocycle_affine_cover : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) → (∀ i i', IsAffineOpen (W i ⊓ W i')) → (∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'')) → ∀ x : GlobalTheory.CechDR.HO1 s, ∃ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), GlobalTheory.CechCmp.IsCocycle W c ∧ GlobalTheory.CechCmp.cmp s W hW c = x := by
  first | exact @GlobalTheory.CechCmp.exists_isCocycle_cmp_eq | exact GlobalTheory.CechCmp.exists_isCocycle_cmp_eq | (intros; apply GlobalTheory.CechCmp.exists_isCocycle_cmp_eq <;> assumption)
