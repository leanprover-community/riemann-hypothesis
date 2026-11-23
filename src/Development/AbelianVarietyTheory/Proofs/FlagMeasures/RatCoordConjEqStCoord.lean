module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopVol

private theorem hJ_smul_right_flag_measures {n : ℕ} (ε : Fin n → Bool) (c : ℂ) (x y : Fin n → ℂ) :
    Formalism.L2.SG.HidaSetting.hJ ε x (c • y) = c * Formalism.L2.SG.HidaSetting.hJ ε x y := by
  unfold Formalism.L2.SG.HidaSetting.hJ
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem ratCoord_conj_eq_stCoord : ∀ (D : D7) (X : HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ s y : X.B.I.Ginf) (τ : D.what₂.Tau) (q : GlobalTheory.LoopV.roots (ptMat w)) (p : Formalism.L2.SG.RealObj.FreeE w), p.1 = q.1 → GlobalTheory.LoopVol.ratCoord X u' w γ s (s * y * s⁻¹) τ q = ((D.host.rdE : ℂ) ^ (q.1.2.1 - q.1.1.1))⁻¹ * Formalism.L2.SG.RealObj.stCoord X u' w γ y (X.pl.symm τ) p := by
  intro D X u' w γ s y τ q p hpq
  obtain ⟨pq, hp⟩ := p
  obtain ⟨qq, hq⟩ := q
  simp only at hpq
  subst hpq

  have hconj : s⁻¹ * (s * y * s⁻¹) * s = y := by group
  have hab : pq.1.val < pq.2.val := hp.1
  have hbr : pq.2.val ≤ D.R.rS := Nat.lt_succ_iff.mp pq.2.isLt
  have hrd : (D.host.rdE : ℂ) ≠ 0 := by
    have h1 := GlobalTheory.RealPlaces.one_le_rdE D
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  unfold GlobalTheory.LoopVol.ratCoord Formalism.L2.SG.RealObj.stCoord
  rw [hconj]
  unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul, Matrix.mulVec_smul, hJ_smul_right_flag_measures]

  have hsplit : D.R.rS - pq.1.val = (pq.2.val - pq.1.val) + (D.R.rS - pq.2.val) := by omega
  rw [hsplit, pow_add]
  field_simp

end GlobalTheory.LoopVol
