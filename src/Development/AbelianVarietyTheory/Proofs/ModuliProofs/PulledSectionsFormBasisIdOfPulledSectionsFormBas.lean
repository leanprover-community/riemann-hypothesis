module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ModelSum

theorem exists_pull_LPow_sec {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (hL : L.IsLB) (N : ℕ) {T T' : Over Z}
    (h : T' ⟶ T) (b : LB.Sec (Out.LPow G L (N : ℤ) T)) :
    ∃ b' : LB.Sec (Out.LPow G L (N : ℤ) T'), ∀ (Y : Scheme.{0}) (r : Y ⟶ (T' ⊗ G).left) (z : Y) (J), Good L z J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) b' r z J =
        sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) b (r ≫ (h ▷ G).left) z J := by
  have hu : (LB.oneGen L (Y := (T' ⊗ G).left)).IsGen := by
    intro (i : PEmpty → L.ι) (j : PEmpty → L.ι)
    simp [LB.oneGen, LB.LinComb, res]
    ext
    erw [Units.val_mul, Units.coe_map, Units.coe_map, Units.val_one, _root_.one_mul, map_one, map_one]
  have hf : FormEq (Sum.elim (fun _ : Fin 1 => (h ▷ G).left ≫ (snd T G).left)
      (PEmpty.elim : PEmpty → ((T' ⊗ G).left ⟶ G.left))) (Sum.elim (fun _ => (N : ℤ)) PEmpty.elim)
      (fun _ : Fin 1 => (snd T' G).left) (fun _ => (N : ℤ)) := by
    intro U _ f
    simp [Fintype.prod_sum_type]
  obtain ⟨b', hb'⟩ := exists_sec hL hf
    (pullMulSec (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) b (h ▷ G).left
      (LB.oneGen L (Y := (T' ⊗ G).left)) hu)
  refine ⟨b', fun Y r z J hJ => (hb' Y r z J hJ).trans ((sval_pullMulSec _ _ _ hu r z hJ).trans ?_)⟩
  rw [val_one, Units.val_one, _root_.mul_one]

theorem basisAlong_id_of_basisAlong : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N n : ℕ) (T T' : Over Z) (h : T' ⟶ T) (b : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T)), L.IsLB → GlobalTheory.LN.BasisAlong G L N h b → ∃ b' : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T'), GlobalTheory.LN.BasisAlong G L N (𝟙 T') b' := by
  intro Z G L N n T T' h b hL hB
  choose b' hb' using fun i => exists_pull_LPow_sec G L hL N h (b i)
  have key : ∀ s c, GlobalTheory.LN.Lin G L N (𝟙 T') b' c s ↔ GlobalTheory.LN.Lin G L N h b c s := by
    intro s c
    have e : ∀ i (z : (T' ⊗ G).left) J, Good L z J →
        sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) (b' i) ((𝟙 T') ▷ G).left z J =
          sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) (b i) (h ▷ G).left z J := by
      intro i z J hJ
      rw [hb' i _ _ z J hJ]
      simp
    unfold GlobalTheory.LN.Lin
    refine forall_congr' fun z => forall_congr' fun J => imp_congr_right fun hJ => ?_
    simp only [e _ z J hJ]
  unfold GlobalTheory.LN.BasisAlong at hB ⊢
  refine ⟨b', fun s => ?_⟩
  obtain ⟨c, hc, hu⟩ := hB s
  exact ⟨c, (key s c).2 hc, fun c' hc' => hu c' ((key s c').1 hc')⟩

end GlobalTheory.ModelSum
