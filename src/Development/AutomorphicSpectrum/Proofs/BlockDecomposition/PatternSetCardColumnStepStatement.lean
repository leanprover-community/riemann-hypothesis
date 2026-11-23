module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternSetCardColumnStep
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

theorem _root_.GlobalTheory.T.pattern_set_card_column_step : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ), j < d →
    (patSet (K := K) (colGe d j)).ncard =
      Fintype.card K ^ j * (patSet (K := K) (colGe d (j + 1))).ncard := by
  intro K _ _ _ d j hj
  classical
  have card_colGe (k : ℕ) :
      (patSet (K := K) (colGe d k)).ncard =
        Fintype.card K ^ Nat.card {p : Fin d × Fin d // colGe d k p.1 p.2} := by
    let A (f : {p : Fin d × Fin d // colGe d k p.1 p.2} → K) : Matrix (Fin d) (Fin d) K :=
      fun i l => if i = l then 1 else if h : colGe d k i l then f ⟨(i, l), h⟩ else 0
    have hunit (f) : IsUnit (A f).det := by
      have htri : (A f).IsUpperTriangular := by
        intro i l h
        change l < i at h
        have hnot : ¬ colGe d k i l := fun hcol => (not_lt_of_gt h) hcol.1
        simp [A, ne_of_gt h, hnot]
      rw [Matrix.det_of_isUpperTriangular htri]
      simp [A]
    let e : patSet (K := K) (colGe d k) ≃ ({p : Fin d × Fin d // colGe d k p.1 p.2} → K) :=
      { toFun := fun u p => (u.val : Matrix (Fin d) (Fin d) K) p.1.1 p.1.2
        invFun := fun f => ⟨Matrix.nonsingInvUnit (A f) (hunit f), by
          intro i l
          change (i = l → A f i l = 1) ∧ (i ≠ l → ¬ colGe d k i l → A f i l = 0)
          exact ⟨fun h => by simp [A, h], fun h hcol => by simp [A, h, hcol]⟩⟩
        left_inv := fun u => by
          apply Subtype.ext
          apply Units.ext
          ext i l
          change A (fun p => (u.val : Matrix (Fin d) (Fin d) K) p.1.1 p.1.2) i l =
            (u.val : Matrix (Fin d) (Fin d) K) i l
          have hu := u.property i l
          by_cases hil : i = l
          · simpa only [A, ite_eq_left hil] using (hu.1 hil).symm
          · by_cases hcol : colGe d k i l
            · simp [A, hil, hcol]
            · simp [A, hil, hcol, hu.2 hil hcol]
        right_inv := fun f => by
          funext p
          change A f p.1.1 p.1.2 = f p
          have hil : p.1.1 ≠ p.1.2 := ne_of_lt p.2.1
          simp [A, hil, p.2] }
    rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := K)]
  rw [card_colGe j, card_colGe (j + 1), natCard_colGe d j hj, pow_add]
