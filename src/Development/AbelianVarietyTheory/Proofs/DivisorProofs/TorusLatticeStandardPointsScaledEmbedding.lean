module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAnalyticSetupPeriodLatticePair
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LaStdEntries

open Formalism.MainNotions.TaylorLogMetric Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7}

def entSub (D : D7) (a b : ℕ) (S : Submodule (𝓞 D.host.E) D.host.E) :
    Submodule (𝓞 D.host.E) (Matrix (Fin b) (Fin a) D.host.E) where
  carrier := {A | ∀ i j, A i j ∈ S}
  add_mem' hA hB i j := by simpa using S.add_mem (hA i j) (hB i j)
  zero_mem' i j := by simp
  smul_mem' o A hA i j := by simpa using S.smul_mem o (hA i j)

theorem homL_le {a b : ℕ} :
    homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D b) ≤ entSub D a b 1 := by
  refine Submodule.span_le.mpr ?_
  intro A hA i j
  have hj : (Pi.single j (1 : D.host.E) : Fin a → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D a := by
    simp only [Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, true_implies]
    intro k
    by_cases hk : k = j
    · subst hk; simp [Submodule.one_eq_range]
    · simp [Pi.single_apply, hk]
  have h := hA _ hj
  simp only [Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at h
  have := h i
  simpa [Matrix.mulVec_single] using this

theorem YYl_le {a b : ℕ} :
    YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D b)
      ≤ entSub D a b (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  refine Submodule.span_le.mpr ?_
  rintro B ⟨x, hx, A, hA, rfl⟩ i j
  obtain ⟨o, ho⟩ := (Submodule.mem_one).1 (homL_le hA i j)
  show x * A i j ∈ _
  rw [← ho, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ o hx

theorem K_mul_mem_AA {c : 𝓞 D.host.K} (hc : c ∈ D.host.ccK) {x : D.host.E}
    (hx : x ∈ D.host.AA0) : ((c : D.host.K) : D.host.E) * x ∈ D.host.AA := by
  show _ ∈ (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0
  refine FractionalIdeal.mul_mem_mul ?_ hx
  rw [FractionalIdeal.mem_coeIdeal]
  exact ⟨_, Ideal.mem_map_of_mem _ hc, rfl⟩

theorem La_std_rep : ∀ {D : D7} (δ : ℂ) {a b : ℕ} (x : Formalism.MainNotions.TaylorLogMetric.VC D a b),
    x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D b) →
    ∃ M : Matrix (Fin b) (Fin a) D.host.E, (∀ i j, M i j ∈ D.host.AA) ∧
      x = δ • Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M := by
  intro D δ a b x hx
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    obtain ⟨c, hc, rfl⟩ := FL.lam_mem D D.host.ccK δ w hw
    refine ⟨((c : D.host.K) : D.host.E) • A, fun i j => ?_, ?_⟩
    · simpa using K_mul_mem_AA hc (YYl_le hA i j)
    · rw [GlobalTheory.MomSetup.embV_smulK, smul_smul]
  | zero => exact ⟨0, fun i j => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).zero_mem, by rw [GlobalTheory.MomSetup.embV_zero, smul_zero]⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨A, hA, rfl⟩ := h1
    obtain ⟨B, hB, rfl⟩ := h2
    exact ⟨A + B, fun i j => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).add_mem (hA i j) (hB i j),
      by rw [GlobalTheory.MomSetup.embV_add, smul_add]⟩
  | neg x _ h =>
    obtain ⟨A, hA, rfl⟩ := h
    exact ⟨-A, fun i j => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).neg_mem (hA i j), by rw [GlobalTheory.MomSetup.embV_neg, smul_neg]⟩

end GlobalTheory.LaStdEntries
