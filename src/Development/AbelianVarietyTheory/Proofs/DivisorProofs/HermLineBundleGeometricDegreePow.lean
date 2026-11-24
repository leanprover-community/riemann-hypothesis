module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.GdegPow

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem isometric_comb_unit (L : HermLB p) (n : ℕ) :
    (comb (fun _ : Unit => L) fun _ => (n : ℤ)).Isometric (L.pow n) :=
  HermLB.icls_eq_iff.1 (by rw [icls_comb, HermLB.icls_pow, Fintype.sum_unique, natCast_zsmul])

theorem lin_unit (c : ℝ) : (lin fun _ : Unit => c) = c • (MvPolynomial.X () : MvPolynomial Unit ℝ) := by
  rw [lin, Fintype.sum_unique, MvPolynomial.C_mul']

theorem gdeg_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : HermLB p) (n : ℕ), gdeg (L.pow n) D = (n : ℝ) ^ D * gdeg L D := by
  intro hC k _ X _ p D hX L n
  obtain ⟨Ψ, hΨ, -⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => L).2
  have key (m : ℕ) : gdeg (L.pow m) D = (m : ℝ) ^ D * Ψ ((MvPolynomial.X () : MvPolynomial Unit ℝ) ^ D) := by
    rw [← (isometric_comb_unit L m).gdeg_eq, ← hΨ fun _ => (m : ℤ)]
    simp only [Int.cast_natCast]
    rw [lin_unit, smul_pow, map_smul, smul_eq_mul]
  have h1 : gdeg L D = Ψ ((MvPolynomial.X () : MvPolynomial Unit ℝ) ^ D) := by
    rw [← (HermLB.icls_eq_iff.1 (by rw [HermLB.icls_pow, one_smul]) : (L.pow 1).Isometric L).gdeg_eq, key 1]
    simp
  rw [key n, h1]

end GlobalTheory.GdegPow
