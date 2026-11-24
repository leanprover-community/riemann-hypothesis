module

import Development.WeilBound.CoreStatements.ThetaDilations.ParAlg
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Matrix

noncomputable section

namespace CompanionTheory.PlacePermOperatorBicommutantSpan

variable {K : Type} [CommRing K] {M : ℕ}

def blk (a b : K) (r : Fin M → K) (c d : K) (r' u w : Fin M → K) (U : Matrix (Fin M) (Fin M) K) :
    Matrix (Fin (M + 2)) (Fin (M + 2)) K :=
  Matrix.of (Fin.cons (Fin.cons a (Fin.cons b r))
    (Fin.cons (Fin.cons c (Fin.cons d r')) fun i => Fin.cons (u i) (Fin.cons (w i) (U i))))

def pm (a b : K) (r : Fin M → K) (d : K) (w : Fin M → K) (U : Matrix (Fin M) (Fin M) K) :
    Matrix (Fin (M + 2)) (Fin (M + 2)) K := blk a b r 0 d 0 0 w U

theorem blk_eta (g : Matrix (Fin (M + 2)) (Fin (M + 2)) K) :
    g = blk (g 0 0) (g 0 1) (fun j => g 0 j.succ.succ) (g 1 0) (g 1 1) (fun j => g 1 j.succ.succ)
      (fun i => g i.succ.succ 0) (fun i => g i.succ.succ 1) (Matrix.of fun i j => g i.succ.succ j.succ.succ) := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.blk_eta <;> assumption

theorem blk_inj {a b c d a' b' c' d' : K} {r s u w r' s' u' w' : Fin M → K} {U U' : Matrix (Fin M) (Fin M) K}
    (h : blk a b r c d s u w U = blk a' b' r' c' d' s' u' w' U') :
    a = a' ∧ b = b' ∧ r = r' ∧ c = c' ∧ d = d' ∧ s = s' ∧ u = u' ∧ w = w' ∧ U = U' := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.blk_inj <;> assumption

theorem blk_mul (a b c d a' b' c' d' : K) (r s u w r' s' u' w' : Fin M → K) (U U' : Matrix (Fin M) (Fin M) K) :
    blk a b r c d s u w U * blk a' b' r' c' d' s' u' w' U' =
      blk (a * a' + b * c' + r ⬝ᵥ u') (a * b' + b * d' + r ⬝ᵥ w') (a • r' + b • s' + r ᵥ* U')
        (c * a' + d * c' + s ⬝ᵥ u') (c * b' + d * d' + s ⬝ᵥ w') (c • r' + d • s' + s ᵥ* U')
        (a' • u + c' • w + U *ᵥ u') (b' • u + d' • w + U *ᵥ w') (vecMulVec u r' + vecMulVec w s' + U * U') := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.blk_mul <;> assumption

theorem pm_mul (a b d a' b' d' : K) (r w r' w' : Fin M → K) (U U' : Matrix (Fin M) (Fin M) K) :
    pm a b r d w U * pm a' b' r' d' w' U' =
      pm (a * a') (a * b' + b * d' + r ⬝ᵥ w') (a • r' + r ᵥ* U') (d * d') (d' • w + U *ᵥ w') (U * U') := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.pm_mul <;> assumption

theorem pm_one : pm (1 : K) 0 (0 : Fin M → K) 1 0 1 = 1 := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.pm_one <;> assumption

theorem blk_map {L : Type} [CommRing L] (φ : K → L) (a b c d : K) (r s u w : Fin M → K) (U : Matrix (Fin M) (Fin M) K) :
    (blk a b r c d s u w U).map φ = blk (φ a) (φ b) (φ ∘ r) (φ c) (φ d) (φ ∘ s) (φ ∘ u) (φ ∘ w) (U.map φ) := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.blk_map <;> assumption

theorem pm_map {L : Type} [CommRing L] (φ : K →+* L) (a b d : K) (r w : Fin M → K) (U : Matrix (Fin M) (Fin M) K) :
    (pm a b r d w U).map φ = pm (φ a) (φ b) (φ ∘ r) (φ d) (φ ∘ w) (U.map φ) := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.pm_map <;> assumption

theorem block_matrix_transpose (a b c d : K) (r s u w : Fin M → K) (U : Matrix (Fin M) (Fin M) K) :
    (blk a b r c d s u w U)ᵀ = blk a c u b d w r s Uᵀ := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.block_matrix_transpose <;> assumption

theorem hypJ_eq (J : Matrix (Fin M) (Fin M) K) : hypJ J = blk 0 1 0 1 0 0 0 0 J := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.hypJ_eq <;> assumption

theorem hypJ_map {L : Type} [CommRing L] (φ : K →+* L) (J : Matrix (Fin M) (Fin M) K) :
    (hypJ J).map φ = hypJ (J.map φ) := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.hypJ_map <;> assumption

theorem hform_eq (s : K →+* K) (J : Matrix (Fin M) (Fin M) K) (x y : Fin M → K) :
    hform s J x y = ((s ∘ x) ᵥ* J) ⬝ᵥ y := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.hform_eq <;> assumption

theorem gram_blk (s : K →+* K) (J : Matrix (Fin M) (Fin M) K) (a b d : K) (r t w : Fin M → K)
    (U : Matrix (Fin M) (Fin M) K) :
    cT s (blk a b r 0 d t 0 w U) * hypJ J * blk a b r 0 d t 0 w U =
      blk 0 (s a * d) (s a • t) (s d * a) (s d * b + s b * d + ((s ∘ w) ᵥ* J) ⬝ᵥ w)
        (s d • r + s b • t + ((s ∘ w) ᵥ* J) ᵥ* U) (a • (s ∘ t)) (b • (s ∘ t) + d • (s ∘ r) + (cT s U * J) *ᵥ w)
        (vecMulVec (s ∘ t) r + vecMulVec (s ∘ r) t + cT s U * J * U) := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.gram_blk <;> assumption

variable (s : K →+* K) (J : Matrix (Fin M) (Fin M) K)

def nM (w : Fin M → K) (z : K) : Matrix (Fin (M + 2)) (Fin (M + 2)) K := pm 1 z (-((s ∘ w) ᵥ* J)) 1 w 1

variable {s J}

theorem nM_unit (hs : ∀ x, s (s x) = x) (hJ : cT s J = J) {w : Fin M → K} {z : K} (hz : z + s z + hform s J w w = 0) :
    cT s (nM s J w z) * hypJ J * nM s J w z = hypJ J := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.nM_unit <;> assumption

theorem iM_unit {U : Matrix (Fin M) (Fin M) K} (hU : cT s U * J * U = J) :
    cT s (pm 1 0 0 1 0 U) * hypJ J * pm 1 0 0 1 0 U = hypJ J := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.iM_unit <;> assumption

theorem mM_unit (hs : ∀ x, s (s x) = x) (a : Kˣ) :
    cT s (pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1) * hypJ J * pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1 = hypJ J := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.mM_unit <;> assumption

theorem nM_mul (w w' : Fin M → K) (z z' : K) :
    nM s J w z * nM s J w' z' = nM s J (w + w') (z + z' - hform s J w w') := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.nM_mul <;> assumption

theorem iM_nM {U : Matrix (Fin M) (Fin M) K} (hU : cT s U * J * U = J) (w : Fin M → K) (z : K) :
    pm 1 0 0 1 0 U * nM s J w z = nM s J (U *ᵥ w) z * pm 1 0 0 1 0 U := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.iM_nM <;> assumption

theorem mM_nM (hs : ∀ x, s (s x) = x) (a : Kˣ) (w : Fin M → K) (z : K) :
    pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1 * nM s J w z =
      nM s J (s a • w) (a * s a * z) * pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1 := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.mM_nM <;> assumption

theorem nim (w : Fin M → K) (z a d : K) (U : Matrix (Fin M) (Fin M) K) :
    nM s J w z * pm 1 0 0 1 0 U * pm a 0 0 d 0 1 = pm a (z * d) (-(((s ∘ w) ᵥ* J) ᵥ* U)) d (d • w) U := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.nim <;> assumption

theorem par_dec (hs : ∀ x, s (s x) = x) {g : Matrix (Fin (M + 2)) (Fin (M + 2)) K} (hg : cT s g * hypJ J * g = hypJ J)
    (h0 : ∀ i : Fin (M + 1), g i.succ 0 = 0) :
    ∃ (w : Fin M → K) (z : K) (U : Matrix (Fin M) (Fin M) K) (a : Kˣ), z + s z + hform s J w w = 0 ∧
      cT s U * J * U = J ∧ g = nM s J w z * pm 1 0 0 1 0 U * pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1 := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.par_dec <;> assumption

def mkU {n : ℕ} (s : K →+* K) {J Ji : Matrix (Fin n) (Fin n) K} (hJ : Ji * J = 1) (g : Matrix (Fin n) (Fin n) K)
    (hg : cT s g * J * g = J) : UJ s J :=
  have h : Ji * cT s g * J * g = 1 := by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s g), hg, hJ]
  ⟨⟨g, Ji * cT s g * J, mul_eq_one_comm.1 h, h⟩, hg⟩

theorem continuous_UJ {n : ℕ} [TopologicalSpace K] [IsTopologicalRing K] {s : K →+* K} (hs : Continuous s)
    {J Ji : Matrix (Fin n) (Fin n) K} (hJ : Ji * J = 1) :
    Topology.IsInducing fun g : UJ s J => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.continuous_UJ <;> assumption

end CompanionTheory.PlacePermOperatorBicommutantSpan
