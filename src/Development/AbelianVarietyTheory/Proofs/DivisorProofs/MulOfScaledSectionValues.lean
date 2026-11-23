module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatSym

theorem VS.mul : ∀ {R Ω : Type} [CommRing R] [IsDomain R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (L : LB Y), L.IsLB → ∀ (x : Sp Ω ⟶ Y) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)) (k l : ℕ) (s s' : FractionRing Ω), GlobalTheory.HeatSym.VS φ L x g k s → GlobalTheory.HeatSym.VS φ L x g l s' → GlobalTheory.HeatSym.VS φ L x g (k + l) (s * s') := by
  intro R Ω _ _ _ φ Y L hL x g k l s s' h h'
  obtain ⟨r, σ, ω, hr, hv, he⟩ := h
  obtain ⟨r', σ', ω', hr', hv', he'⟩ := h'
  have hF : FormEq (Sum.elim (fun _ : Fin 1 => 𝟙 Y) (fun _ : Fin 1 => 𝟙 Y))
      (Sum.elim (fun _ : Fin 1 => (k : ℤ)) (fun _ : Fin 1 => (l : ℤ)))
      (fun _ : Fin 1 => 𝟙 Y) (fun _ => ((k + l : ℕ) : ℤ)) := by
    intro U _ f
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.prod_singleton]
    push_cast
    rw [zpow_add]
  obtain ⟨σ'', hσ''⟩ := exists_sec hL hF (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.mulSec σ σ')
  refine ⟨r * r', σ'', ω * ω', mul_ne_zero hr hr', ?_, ?_⟩
  · intro Z q z J hJ
    rw [hσ'' Z (q ≫ x) z J hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec σ σ' (q ≫ x) z hJ, hv Z q z J hJ, hv' Z q z J hJ,
      map_mul, gs_mul q z ⊤ trivial, pow_add, Units.val_mul]
    ring
  · rw [map_mul, map_mul, map_mul, he, he']
    ring

end GlobalTheory.HeatSym
