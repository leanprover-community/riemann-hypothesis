module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem fock_add {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (q : ℤ) (a b : Fin g → ℂ)
    (θ : (Fin g → ℂ) → ℂ) :
    fock Hm q (a + b) θ = fun z => Complex.exp ((q : ℂ) * Real.pi * Complex.I * ((hermForm Hm a b).im : ℂ)) *
      fock Hm q a (fock Hm q b θ) z := by
  have hl : ∀ z z' w, hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := fun z z' w => by
    simp [hermForm, add_dotProduct]
  have hr : ∀ z w w', hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := fun z w w' => by
    simp [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]
  have hs : hermForm Hm b a = star (hermForm Hm a b) := by
    rw [hermForm, hermForm, ← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq,
      Matrix.dotProduct_mulVec]
  have hsc : hermForm Hm b a = hermForm Hm a b - 2 * Complex.I * ((hermForm Hm a b).im : ℂ) := by
    rw [hs]
    apply Complex.ext <;> simp
    ring
  funext z
  simp only [fock]
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Complex.exp_add, ← Complex.exp_add, add_assoc z a b]
  congr 2
  simp only [hl, hr, hsc]
  ring

theorem fock_sq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) (a : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ) :
    fock Hm ((N : ℤ) ^ 2) a (fun z => θ ((N : ℂ) • z)) = fun z => fock Hm 1 ((N : ℂ) • a) θ ((N : ℂ) • z) := by
  have h : ∀ z w, hermForm Hm ((N : ℂ) • z) ((N : ℂ) • w) = (N : ℂ) ^ 2 * hermForm Hm z w := fun z w => by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      star_natCast]
    ring
  funext z
  simp only [fock, h, smul_add]
  congr 2
  push_cast
  ring

theorem fock_laws : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ (q : ℤ) (a b : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ), fock Φ.Hm q (a + b) θ = fun z => Complex.exp ((q : ℂ) * Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ)) * fock Φ.Hm q a (fock Φ.Hm q b θ) z) ∧ (∀ (N : ℕ) (a : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ), fock Φ.Hm ((N : ℤ) ^ 2) a (fun z => θ ((N : ℂ) • z)) = fun z => fock Φ.Hm 1 ((N : ℂ) • a) θ ((N : ℂ) • z)) ∧ ∀ θ, Φ.IsTh 1 θ → ∀ a ∈ Φ.lat, fock Φ.Hm 1 a θ = fun z => Φ.χ a * θ z := by
  intro S A _ _ L x0 g Φ
  refine ⟨fun q a b θ => fock_add Φ.herm q a b θ, fun N a θ => fock_sq Φ.Hm N a θ, fun θ hθ a ha => ?_⟩
  funext z
  simp only [fock, hθ.2 a ha z, AnFr.fac, zpow_one]
  have : Complex.exp (-(((1 : ℤ) : ℂ) * Real.pi * hermForm Φ.Hm z a) - ((1 : ℤ) : ℂ) * Real.pi * hermForm Φ.Hm a a / 2) *
      Complex.exp (Real.pi * hermForm Φ.Hm z a + Real.pi / 2 * hermForm Φ.Hm a a) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    push_cast
    ring
  linear_combination (Φ.χ a * θ z) * this

end GlobalTheory.AnVal
