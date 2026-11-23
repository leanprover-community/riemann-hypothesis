module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
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

set_option autoImplicit false

noncomputable section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.HTPair.QuotIsog

variable {p : ℕ} {O : Type} [CommRing O] {G H : PDivGroup p O} (τ : QuotTower G)

theorem j_injective (m : ℕ) : Function.Injective (τ.j m) := fun a b h => by
  rw [← τ.ρ_j m a, ← τ.ρ_j m b, h]

theorem pDivSubgroupQuotientTower_r_s_eq_s_res (m : ℕ) (a : G.A (m + 1)) : τ.r m (τ.s (m + 1) a) = τ.s m (G.res m a) := by
  apply j_injective τ m
  rw [τ.j_r, τ.j_s, τ.j_s, G.res_mulP, G.mulP_res]

theorem s_res_j (m : ℕ) (b : τ.B m) : τ.s m (G.res m (τ.j m b)) = mulBy O _ p b := by
  apply j_injective τ m
  rw [τ.j_s, G.mulP_res, map_mulBy]

theorem ker_le (m : ℕ) : torsionIdeal (R := O) (A := τ.B m) (p ^ m) ≤
    RingHom.ker (((G.res m).comp (τ.j m) : τ.B m →ₐc[O] G.A m) : τ.B m →ₐ[O] G.A m) := by
  refine (kerIdeal_le_ker_iff _ _).2 fun c => ?_
  change ((G.res m).comp (τ.j m)) (mulBy O _ (p ^ m) c) = _
  rw [map_mulBy, G.mulBy_pow_self, CoalgHomClass.counit_comp_apply]

variable [Fact p.Prime]

def toQuot (q : ∀ m, τ.B m →ₐc[O] H.A m) (hs : ∀ m, Function.Surjective (q m))
    (hk : ∀ m, RingHom.ker (q m) = torsionIdeal (R := O) (A := τ.B m) (p ^ m))
    (hc : ∀ m b, H.res m (q (m + 1) b) = q m (τ.r m b)) : G ⟶ H where
  app m := liftSurj (q m) (hs m) ((G.res m).comp (τ.j m)) ((hk m).le.trans (ker_le τ m))
  comm n := BialgHom.ext fun c => by
    obtain ⟨b, rfl⟩ := hs (n + 1) c
    rw [BialgHom.comp_apply, BialgHom.comp_apply, hc, liftSurj_apply, liftSurj_apply,
      BialgHom.comp_apply, BialgHom.comp_apply, ← τ.j_r]

theorem toQuot_app_q (q : ∀ m, τ.B m →ₐc[O] H.A m) (hs : ∀ m, Function.Surjective (q m))
    (hk : ∀ m, RingHom.ker (q m) = torsionIdeal (R := O) (A := τ.B m) (p ^ m))
    (hc : ∀ m b, H.res m (q (m + 1) b) = q m (τ.r m b)) (m : ℕ) (b : τ.B m) :
    (toQuot τ q hs hk hc).app m (q m b) = G.res m (τ.j m b) :=
  liftSurj_apply ..

def fromQuot (q : ∀ m, τ.B m →ₐc[O] H.A m)
    (hc : ∀ m b, H.res m (q (m + 1) b) = q m (τ.r m b)) : H ⟶ G where
  app m := (q m).comp (τ.s m)
  comm n := BialgHom.ext fun a => by
    change H.res n (q (n + 1) (τ.s (n + 1) a)) = q n (τ.s n (G.res n a))
    rw [hc, pDivSubgroupQuotientTower_r_s_eq_s_res]

end GlobalTheory.HTPair.QuotIsog
