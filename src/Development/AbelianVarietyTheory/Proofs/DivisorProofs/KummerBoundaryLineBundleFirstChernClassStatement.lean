module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerBoundaryLineBundleFirstChernClass
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.kummerBoundary_lineBundle_firstChernClass : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0), Mono κ →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U))) →
  ∀ (z : Cocycle (res ℤ (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1) (s : ℤˣ),
  (∀ (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0) (ψ : cokernel κ ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 1),
      κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) → cokernel.π κ ≫ ψ = φ ≫ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).d 0 1 →
      ∀ w : Cocycle (sgl (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1, sglι (cokernel κ) ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug (cokernel κ))) z (zero_add 1)) = s • CohomologyClass.mk w) →
  ∀ (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → ∀ y : H ℤ E (cokernel κ) 1,
    HK.post ℤ _ (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) 1 y = picClass L →
    HK.ext ℤ _ z 1 (1 + 1) rfl y = s • restrH (Int.castRingHom (ZMod q)) E (tw q 1) (1 + 1) (c1 q L) := by
  first
  | exact @GlobalTheory.EtC.KumPic.kummer_boundary_picClass
  | exact GlobalTheory.EtC.KumPic.kummer_boundary_picClass
  | (intros; apply GlobalTheory.EtC.KumPic.kummer_boundary_picClass <;> assumption)
