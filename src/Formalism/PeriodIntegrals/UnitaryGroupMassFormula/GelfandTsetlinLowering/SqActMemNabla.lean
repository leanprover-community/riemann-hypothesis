module

public import Formalism.PeriodIntegrals.GTDefs
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.AdjBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.Params

@[expose] public section

noncomputable section

namespace PI.WGL.Adj

open Formalism.BasicNotions MvPolynomial

def gStar {N : ℕ} (g : GL (Fin N) ℂ) : GL (Fin N) ℂ where
  val := Matrix.conjTranspose (g : Matrix (Fin N) (Fin N) ℂ)
  inv := Matrix.conjTranspose ((g⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
  val_inv := simp [← Matrix.conjTranspose_mul]
  inv_val := simp [← Matrix.conjTranspose_mul]

theorem gStar_val {N : ℕ} (g : GL (Fin N) ℂ) :
    ((gStar g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = Matrix.conjTranspose (g : Matrix (Fin N) (Fin N) ℂ) := rfl

theorem gStar_gStar {N : ℕ} (g : GL (Fin N) ℂ) : gStar (gStar g) = g := by
  ext i j; simp [gStar_val]

def cU (a : ℂˣ) : ℂˣ := Units.map (starRingEnd ℂ : ℂ →* ℂ) a

theorem cU_zpow_val (a : ℂˣ) (e : ℤ) : ((cU a ^ e : ℂˣ) : ℂ) = star ((a ^ e : ℂˣ) : ℂ) := by
  unfold cU
  rw [← map_zpow, Units.coe_map]
  rfl

theorem embGL_gStar {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) :
    embGL ℂ n N h (gStar g) = gStar (embGL ℂ n N h g) := by
  have key : ∀ p q : Fin n ⊕ Fin 1,
      Matrix.fromBlocks (Matrix.conjTranspose (g : Matrix (Fin n) (Fin n) ℂ)) 0 0 1 p q =
        (starRingEnd ℂ) (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 1 q p) := by
    rintro (p | p) (q | q)
    · simp [Matrix.conjTranspose_apply]
    · simp
    · simp
    · have hp : p = q := Subsingleton.elim _ _
      subst hp; simp
  ext i j
  simp only [embGL, blkHom, gStar_val, Matrix.conjTranspose_apply]
  simp
  exact key _ _

theorem lastGL_cU (N : ℕ) (a : ℂˣ) : lastGL ℂ N (cU a) = gStar (lastGL ℂ N a) := by
  ext i j
  simp only [lastGL, diagGL, gStar_val, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; split_ifs <;> simp [cU]
  · have hji : j ≠ i := fun e => hij e.symm
    simp [hij, hji]

theorem detPow_gStar {N : ℕ} (g : GL (Fin N) ℂ) (k : ℤ) :
    detPow ℂ N (gStar g) k = star (detPow ℂ N g k) := by
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, star_zpow₀]
  congr 1
  simp [gStar_val, Matrix.det_conjTranspose]

theorem sqAct_mem_nabla {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ nablaSq ℂ N lam) : sqAct ℂ N lam g f ∈ nablaSq ℂ N lam := by
  unfold sqAct
  exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N lam.natW _ f hf)

theorem sqAct_smul {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (c : ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqAct ℂ N lam g (c • f) = c • sqAct ℂ N lam g f := by
  unfold sqAct
  rw [map_smul, smul_comm]

theorem nf_sqAct_adj {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (sqAct ℂ N lam g x) y = normFock lam x (sqAct ℂ N lam (gStar g) y) := by
  have hm : Matrix.conjTranspose (Matrix.transpose (g : Matrix (Fin N) (Fin N) ℂ)) =
      Matrix.transpose ((gStar g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
    ext i j; simp [gStar_val, Matrix.conjTranspose_apply]
  have hf : Formalism.REAL.fockF (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.transpose (g : Matrix (Fin N) (Fin N) ℂ)) x) y =
      Formalism.REAL.fockF x (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
        (Matrix.transpose ((gStar g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) y) := by
    rw [Formalism.GradedWeylDivisibility.fockRowAdj, hm]
  unfold sqAct
  rw [nf_smul_left, nf_smul_right, detPow_gStar, star_star]
  unfold normFock
  rw [hf]

theorem nf_sqAct_adj' {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam x (sqAct ℂ N lam g y) = normFock lam (sqAct ℂ N lam (gStar g) x) y := by
  rw [nf_sqAct_adj, gStar_gStar]

theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by have := lam.anti hij; linarith)

theorem extremal_mem {N : ℕ} (lam : DomWeight N) : extremal ℂ N lam ∈ nablaSq ℂ N lam :=
  Formalism.GradedWeylDivisibility.hwMem ℂ N N le_rfl lam.natW (natW_anti lam)

theorem extremal_ne {N : ℕ} (lam : DomWeight N) : extremal ℂ N lam ≠ 0 :=
  Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW

end PI.WGL.Adj
