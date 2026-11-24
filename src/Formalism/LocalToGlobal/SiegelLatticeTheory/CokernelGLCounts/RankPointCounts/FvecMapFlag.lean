module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PairingOmegaPrimeZ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem omp_congr {F G : FlagG S r T} {F' G' : FlagG S r T'} (h : ∀ a, F.fvec a = G.fvec a)
    (h' : ∀ a, F'.fvec a = G'.fvec a) : omp F F' = omp G G' ∧ Zhat F F' = Zhat G G' := by
  have hF : F.fvec = G.fvec := funext h
  have hF' : F'.fvec = G'.fvec := funext h'
  have hZ : Zhat F F' = Zhat G G' := by
    unfold Zhat
    first
      | rw [hF, hF']
  refine ⟨?_, hZ⟩
  unfold omp
  rw [hZ, hF']

theorem fvec_mapFlag (g : S.V ≃ₗ[E] S.V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (b : Fin (r + 1)) :
    (mapFlag g hg F).fvec b = g (F.fvec b) := by
  unfold FlagG.fvec
  induction b using Fin.lastCases with
  | last => simp [mapFlag]
  | cast i => simp [mapFlag]

theorem coef_mat (F : FlagG S r T) (s : S.V →ₗ[E] S.V) (hs : ∀ j, ∀ x ∈ F.Xa (j + 1), s x - x ∈ F.Xa j)
    (hz : s F.z - F.z ∈ F.X) :
    ∃ M : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ b, s (F.fvec b) = ∑ c, M c b • F.fvec c) ∧ M.det = 1 ∧
      ∀ c, M (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
  have hcolE : ∀ b' : Fin r, ∃ l : Fin r →₀ E, (∀ i : Fin r, ¬ i.1 < b'.1 → l i = 0) ∧
      s (F.e b') = F.e b' + ∑ i, l i • F.e i := by
    intro b'
    have hmem : F.e b' ∈ F.Xa (b'.1 + 1) := Submodule.subset_span ⟨b', Nat.lt_succ_self _, rfl⟩
    have h1 := hs b'.1 (F.e b') hmem
    obtain ⟨l, hl, hl2⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 h1
    refine ⟨l, fun i hi => (Finsupp.mem_supported' E l).1 hl i hi, ?_⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hl2
    rw [hl2]
    abel
  choose l hl0 hl using hcolE
  obtain ⟨cz, hcz⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hz
  let M : Matrix (Fin (r + 1)) (Fin (r + 1)) E := Matrix.of fun c b =>
    Fin.lastCases (motive := fun _ => E)
      (Fin.lastCases (motive := fun _ => E) 1 (fun i => cz i) c)
      (fun b' => Fin.lastCases (motive := fun _ => E) 0 (fun i => (if i = b' then 1 else 0) + l b' i) c) b
  have hMcol : ∀ b, s (F.fvec b) = ∑ c, M c b • F.fvec c := by
    intro b
    induction b using Fin.lastCases with
    | last =>
      rw [Fin.sum_univ_castSucc]
      simp only [M, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, Formalism.MainNotions.S.FlagG.fvec,
        Fin.snoc_last, Fin.snoc_castSucc, one_smul]
      have h2 : s F.z = F.z + ∑ i, cz i • F.e i := by
        rw [hcz]
        abel
      rw [h2, add_comm]
    | cast b' =>
      rw [Fin.sum_univ_castSucc]
      simp only [M, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, Formalism.MainNotions.S.FlagG.fvec,
        Fin.snoc_last, Fin.snoc_castSucc, zero_smul, add_zero, add_smul, Finset.sum_add_distrib, ite_smul,
        one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact hl b'
  have hdiag : ∀ i, M i i = 1 := by
    intro i
    induction i using Fin.lastCases with
    | last => simp [M]
    | cast i => simp [M, hl0 i i (lt_irrefl _)]
  have htri : M.BlockTriangular id := by
    intro i j hij
    induction j using Fin.lastCases with
    | last => exact absurd hij (not_lt.2 (Fin.le_last i))
    | cast j =>
      induction i using Fin.lastCases with
      | last => simp [M]
      | cast i =>
        have hji : j < i := by simpa using hij
        have hne : i ≠ j := (ne_of_lt hji).symm
        simp [M, hne, hl0 j i (not_lt.2 (le_of_lt hji))]
  refine ⟨M, hMcol, ?_, ?_⟩
  · rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => hdiag i
  · intro c
    induction c using Fin.lastCases with
    | last => simp [M]
    | cast c => simp [M, Fin.castSucc_ne_last]

end Formalism.L2.SG.NGCut.NormalVectorPairings
