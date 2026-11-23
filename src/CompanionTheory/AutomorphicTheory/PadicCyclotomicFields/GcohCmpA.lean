module

import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmpA
public import GroundTheory.ProfiniteCohomology.CupProducts
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import GroundTheory.ProfiniteCohomology.FilteredHomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

attribute [local instance 2000] Rep.hV2

section Core

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [IsDiscreteRep A]

theorem coc_inj (n : ℕ) {x y : cocycles A n}
    (h : cochainOf A (cocycleι A n x) = cochainOf A (cocycleι A n y)) : x = y := by
  apply PositivityTheory.LocalTateOrthogonality.Gcoh.coc_inj <;> assumption

theorem exists_coc (n : ℕ) (c : (Fin n → G) → A) (hc : IsLocallyConstant c)
    (hd : (inhomogeneousCochains.d A n).hom c = 0) :
    ∃ x : cocycles A n, cochainOf A (cocycleι A n x) = c := by
  apply PositivityTheory.LocalTateOrthogonality.Gcoh.exists_coc <;> assumption

theorem pi_succ_eq_zero_iff (n : ℕ) (x : cocycles A (n + 1)) :
    cohomologyπ A (n + 1) x = 0 ↔ ∃ w : (Fin n → G) → A, IsLocallyConstant w ∧
      (inhomogeneousCochains.d A n).hom w = cochainOf A (cocycleι A (n + 1) x) := by
  apply PositivityTheory.LocalTateOrthogonality.Gcoh.pi_succ_eq_zero_iff <;> assumption

theorem pi_zero_eq_zero_iff (x : cocycles A 0) :
    cohomologyπ A 0 x = 0 ↔ cochainOf A (cocycleι A 0 x) = 0 := by
  apply PositivityTheory.LocalTateOrthogonality.Gcoh.pi_zero_eq_zero_iff <;> assumption

theorem core_hom {Z : Type} [AddCommGroup Z] (n : ℕ) (φ : Z →+ ((Fin n → G) → A))
    (hex : ∀ z, ∃ x : cocycles A n, cochainOf A (cocycleι A n x) = φ z)
    (hsurj : ∀ x : cocycles A n, ∃ z, cochainOf A (cocycleι A n x) = φ z) :
    ∃ f : Z →+ cohomology A n, Function.Surjective f ∧
      ∀ z x, cochainOf A (cocycleι A n x) = φ z → f z = cohomologyπ A n x := by
  apply PositivityTheory.LocalTateOrthogonality.Gcoh.core_hom <;> assumption

theorem core_quot {R Z : Type} [CommRing R] [AddCommGroup Z] [Module R Z] (B : Submodule R Z)
    (n : ℕ) (φ : Z →+ ((Fin n → G) → A))
    (hex : ∀ z, ∃ x : cocycles A n, cochainOf A (cocycleι A n x) = φ z)
    (hsurj : ∀ x : cocycles A n, ∃ z, cochainOf A (cocycleι A n x) = φ z)
    (hB : ∀ z x, cochainOf A (cocycleι A n x) = φ z → (cohomologyπ A n x = 0 ↔ z ∈ B)) :
    ∃ e : (Z ⧸ B) ≃+ cohomology A n,
      ∀ z x, cochainOf A (cocycleι A n x) = φ z →
        e (Submodule.Quotient.mk z) = cohomologyπ A n x := by
  apply PositivityTheory.LocalTateOrthogonality.Gcoh.core_quot <;> assumption

end Core

theorem neg_one_pow_smul' {S V : Type} [Ring S] [AddCommGroup V] [Module S V] (j : ℕ) (v : V) :
    (-1 : S) ^ j • v = (-1 : ℤ) ^ j • v := by
  apply PositivityTheory.LocalTateOrthogonality.Gcoh.neg_one_pow_smul' <;> assumption

section Cmp

variable {k G : Type} [CommRing k] [Group G]
  {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  (rho : Representation R G M) (A : Rep.{0} k G) (e : M ≃+ A.V)
  (he : ∀ g m, e (rho g m) = A.ρ g (e m))

theorem dn_app (n : ℕ) (f : (Fin n → G) → M) (g : Fin (n + 1) → G) :
    dn rho n f g = rho (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := by
  apply PositivityTheory.LocalTateOrthogonality.Gcoh.dn_app <;> assumption

include he in
theorem d_comp (n : ℕ) (f : (Fin n → G) → M) :
    (inhomogeneousCochains.d A n).hom (fun s => e (f s)) = fun s => e (dn rho n f s) := by
  apply PositivityTheory.LocalTateOrthogonality.Gcoh.d_comp <;> assumption

theorem dn_zero (f : (Fin 0 → G) → M) (s : Fin 1 → G) :
    dn rho 0 f s = rho (s 0) (f default) - f default := by
  apply PositivityTheory.LocalTateOrthogonality.Gcoh.dn_zero <;> assumption

theorem dn_one (f : G → M) (s : Fin 2 → G) :
    dn rho 1 (fun t => f (t 0)) s = rho (s 0) (f (s 1)) - f (s 0 * s 1) + f (s 0) := by
  apply PositivityTheory.LocalTateOrthogonality.Gcoh.dn_one <;> assumption

theorem dn_two (f : G × G → M) (s : Fin 3 → G) :
    dn rho 2 (fun t => f (t 0, t 1)) s =
      rho (s 0) (f (s 1, s 2)) - f (s 0 * s 1, s 2) + f (s 0, s 1 * s 2) - f (s 0, s 1) := by
  apply PositivityTheory.LocalTateOrthogonality.Gcoh.dn_two <;> assumption

end Cmp

end CompanionTheory.LocalTateOrthogonality.Gcoh
