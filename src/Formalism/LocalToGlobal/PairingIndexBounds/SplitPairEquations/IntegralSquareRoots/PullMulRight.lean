module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Reduction
public import Formalism.LocalRingCardinality.SpanPowerMembership.RelDet
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.CharacterFactorUnitaryAction
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdeal
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.PullIopOf
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.ReductionOf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def J1at (B : Ker.Base D cc δ) (N N' : ℕ)
    (γ : letI := D.host.cmStar; Matrix.unitaryGroup (Fin N) D.host.E) : Prop :=
  letI := D.host.cmStar
  TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (1 : Matrix (Fin N') (Fin N') D.host.E) (B.thZero N N') =
    (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) •
      B.thHalf N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))

def J2at (B : Ker.Base D cc δ) (N N' : ℕ)
    (γ' : letI := D.host.cmStar; Matrix.unitaryGroup (Fin N') D.host.E) : Prop :=
  letI := D.host.cmStar
  TaylorLogMetric.pull D B.tor (1 : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.thZero N N') =
    (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) ^ (N / 2) •
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')))
        (B.thZero N N')

theorem pull_mul_left {N N' : ℕ} (γ₁ γ₂ : Matrix (Fin N) (Fin N) D.host.E) (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) (γ₁ * γ₂) (1 : Matrix (Fin N') (Fin N') D.host.E) G =
      TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) γ₁ 1 (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) γ₂ 1 G) := by
  funext z
  simp only [TaylorLogMetric.pull, TaylorLogMetric.tor0]
  congr 1
  funext τ
  simp [Matrix.map_one, Matrix.map_mul]
  exact (Matrix.mul_assoc _ _ _).symm

theorem pull_mul_right {N N' : ℕ} (γ₁ γ₂ : Matrix (Fin N') (Fin N') D.host.E) (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) (1 : Matrix (Fin N) (Fin N) D.host.E) (γ₁ * γ₂) G =
      TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) 1 γ₁ (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) 1 γ₂ G) := by
  funext z
  simp only [TaylorLogMetric.pull, TaylorLogMetric.tor0]
  congr 1
  funext τ
  simp [Matrix.map_one, Matrix.map_mul, Matrix.mul_assoc, Matrix.conjTranspose_mul]
  rfl

variable {B : Ker.Base D cc δ}

theorem J1at_mul (hL : B.LatAll) (hTL : Tr0L D B.tor) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (h0 : B.ThZeroMem N N') :
    letI := D.host.cmStar
    ∀ γ₁ γ₂ : Matrix.unitaryGroup (Fin N) D.host.E, J1at B N N' γ₁ → J1at B N N' γ₂ → J1at B N N' (γ₁ * γ₂) := by
  letI := D.host.cmStar
  intro γ₁ γ₂ j1 j2
  have e1 : ((1 : Matrix.unitaryGroup (Fin N') D.host.E) : Matrix (Fin N') (Fin N') D.host.E) = 1 := rfl
  have em : ((γ₁ * γ₂ : Matrix.unitaryGroup (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) =
      (γ₁ : Matrix (Fin N) (Fin N) D.host.E) * (γ₂ : Matrix (Fin N) (Fin N) D.host.E) := rfl
  have s1 := smulSD D N (StandardLatticesGL3.stdL D N) γ₁ (sd0 N)
  have s2 := smulSD D N (StandardLatticesGL3.stdL D N) γ₂ (sd0 N)
  have s12 := smulSD D N _ γ₁ s2
  have p := (pullIop_of hL N N' (StandardLatticesGL3.stdL D N) (SDLat.smulLat (γ₂ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))
    (StandardLatticesGL3.stdL D N') (StandardLatticesGL3.stdL D N') γ₁ 1 hN hN' (sd0 N) s2 (sd0 N') (sd0 N') (B.thZero N N')
    (mem_ThSp_of' _ _ _ _ h0)).2
  rw [e1, Formalism.BasicNotions.Examples₂.smulLat_one] at p
  have t := hTL N N' _ _ hN hN' s1 s12 _ (mem_ThSp_of' _ _ _ _ h0)
  unfold J1at at j1 j2 ⊢
  rw [em, pull_mul_left, j2, pull_smul]
  show _ • TaylorLogMetric.pull D B.tor _ _ (TaylorLogMetric.Iop D B.tor _ _ (B.thZero N N')) = _
  rw [p, j1, Iop_smulF]
  show _ • _ • TaylorLogMetric.Iop D B.tor _ _ (TaylorLogMetric.Iop D B.tor _ _ (B.thZero N N')) = _
  rw [t, smul_smul, Formalism.BasicNotions.Examples₂.smulLat_mul, Matrix.det_mul, star_mul']
  simp only [map_mul, Finset.prod_mul_distrib, mul_pow]
  rw [mul_comm]
  rfl

theorem J2at_mul (hL : B.LatAll) (hTR : Tr0R D B.tor) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (h0 : B.ThZeroMem N N') :
    letI := D.host.cmStar
    ∀ γ₁ γ₂ : Matrix.unitaryGroup (Fin N') D.host.E, J2at B N N' γ₁ → J2at B N N' γ₂ → J2at B N N' (γ₁ * γ₂) := by
  letI := D.host.cmStar
  intro γ₁ γ₂ j1 j2
  have e1 : ((1 : Matrix.unitaryGroup (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) = 1 := rfl
  have em : ((γ₁ * γ₂ : Matrix.unitaryGroup (Fin N') D.host.E) : Matrix (Fin N') (Fin N') D.host.E) =
      (γ₁ : Matrix (Fin N') (Fin N') D.host.E) * (γ₂ : Matrix (Fin N') (Fin N') D.host.E) := rfl
  have s1 := smulSD D N' (StandardLatticesGL3.stdL D N') γ₁ (sd0 N')
  have s2 := smulSD D N' (StandardLatticesGL3.stdL D N') γ₂ (sd0 N')
  have s12 := smulSD D N' _ γ₁ s2
  have p := (pullIop_of hL N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')
    (SDLat.smulLat (γ₂ : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')) 1 γ₁ hN hN' (sd0 N) (sd0 N) (sd0 N') s2
    (B.thZero N N') (mem_ThSp_of' _ _ _ _ h0)).2
  rw [e1, Formalism.BasicNotions.Examples₂.smulLat_one] at p
  have t := hTR N N' _ _ hN hN' s1 s12 _ (mem_ThSp_of' _ _ _ _ h0)
  unfold J2at at j1 j2 ⊢
  rw [em, pull_mul_right, j2, pull_smul, p, j1, Iop_smulF, t, smul_smul, Formalism.BasicNotions.Examples₂.smulLat_mul, Matrix.det_mul]
  simp only [map_mul, Finset.prod_mul_distrib, mul_pow]
  rw [mul_comm]

end Formalism.L2.PairingIndexBounds.Eq.J
