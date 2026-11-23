module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB.MV

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def addF (k : Type) [CommRing k] (d : ℕ) : Fin d → PS k 2 d :=
  fun j => MvPowerSeries.X ((0 : Fin 2), j) + MvPowerSeries.X ((1 : Fin 2), j)

section Pair

variable {k : Type} [CommRing k] {σ : Type}

theorem coeff_iter_pderiv (i : σ) (c : ℕ) (g : MvPowerSeries σ k) (n : σ →₀ ℕ) :
    coeff n ((pderiv i)^[c] g) =
      coeff (n + c • Finsupp.single i 1) g * ((n i + 1).ascFactorial c : k) := by
  induction c generalizing n g with
  | zero => simp
  | succ c ih =>
    rw [Function.iterate_succ_apply, ih, MvPowerSeries.coeff_pderiv]
    have h1 : n + c • Finsupp.single i 1 + Finsupp.single i 1 = n + (c + 1) • Finsupp.single i 1 := by
      rw [add_smul, one_smul, add_assoc]
    have h2 : ((n + c • Finsupp.single i 1 : σ →₀ ℕ)) i = n i + c := by simp
    rw [h1, h2, Nat.ascFactorial_succ]
    push_cast
    ring

theorem coeff_fold {ι : Type} (cd : ι → σ) (hc : Function.Injective cd) (m : ι → ℕ) (f : MvPowerSeries σ k) :
    ∀ (L : List ι), L.Nodup → ∀ n : σ →₀ ℕ,
      coeff n (L.foldr (fun l g => (pderiv (cd l))^[m l] g) f) =
        coeff (n + (L.map fun l => m l • Finsupp.single (cd l) 1).sum) f *
          (L.map fun l => ((n (cd l) + 1).ascFactorial (m l) : k)).prod := by
  intro L
  induction L with
  | nil => intro _ n; simp
  | cons l L ih =>
    intro hnd n
    rw [List.nodup_cons] at hnd
    rw [List.foldr_cons, coeff_iter_pderiv, ih hnd.2]
    have hprod : (L.map fun l' => (((n + m l • Finsupp.single (cd l) 1 : σ →₀ ℕ) (cd l') + 1).ascFactorial (m l') : k)).prod
        = (L.map fun l' => ((n (cd l') + 1).ascFactorial (m l') : k)).prod := by
      congr 1
      apply List.map_congr_left
      intro l' hl'
      have hne : cd l ≠ cd l' := fun h => hnd.1 (by rw [hc h]; exact hl')
      simp [hne]
    rw [hprod, List.map_cons, List.sum_cons, List.map_cons, List.prod_cons, add_assoc]
    ring

end Pair

section Pair2

variable {k : Type} [CommRing k]

end Pair2

end ReciprocityTheory.ChartRestriction.G.TB.MV
