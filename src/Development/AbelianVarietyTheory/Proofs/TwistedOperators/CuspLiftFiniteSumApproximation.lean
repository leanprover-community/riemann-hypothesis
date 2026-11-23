module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DnFormApprox

variable {D : D7}

theorem autSm_cusp_of_mem_cusp (N : GlobalTheory.Grid.Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsAutFunSm θ N.V (Φ v) ∧ IsCuspFun N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have h0 : IsCuspFun N.V (0 : GA D N.V → ℂ) := fun r C hC μ 𝓕 hμ h𝓕 g => by simp
  have hz : IsAutFunSm θ N.V (0 : GA D N.V → ℂ) := GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ N.V
  have hU' : ∀ w, IsAutFunSm θ N.V (U w) ∧ IsCuspFun N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => ⟨hx.aut w, hx.cusp w⟩
    | zero => exact fun w => ⟨hz, h0⟩
    | add x y _ _ hx hy => exact fun w => ⟨GlobalTheory.MultMem.isAutFunSm_add (hx w).1 (hy w).1,
        GlobalTheory.MultMem.isCuspFun_add (hx w).1.toIsAutFun (hy w).1.toIsAutFun (hx w).2 (hy w).2⟩
    | smul c x _ hx => exact fun w => ⟨GlobalTheory.MultMem.isAutFunSm_smul c (hx w).1, GlobalTheory.MultMem.isCuspFun_smul c (hx w).2⟩
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using ⟨GlobalTheory.MultMem.isAutFunSm_smul r (hU' f).1, GlobalTheory.MultMem.isCuspFun_smul r (hU' f).2⟩
  | add x y hx hy => simpa using ⟨GlobalTheory.MultMem.isAutFunSm_add hx.1 hy.1,
      GlobalTheory.MultMem.isCuspFun_add hx.1.toIsAutFun hy.1.toIsAutFun hx.2 hy.2⟩

theorem autSm_cusp_sum {V : HSp D} {θ : InfFam D} (K : Finset ℕ) (u : ℕ → GA D V → ℂ)
    (hu : ∀ k ∈ K, IsAutFunSm θ V (u k) ∧ IsCuspFun V (u k)) :
    IsAutFunSm θ V (∑ k ∈ K, u k) ∧ IsCuspFun V (∑ k ∈ K, u k) := by
  induction K using Finset.induction_on with
  | empty =>
    have h0 : IsCuspFun V (0 : GA D V → ℂ) := fun r C hC μ 𝓕 hμ h𝓕 g => by simp
    rw [Finset.sum_empty]
    exact ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ V, h0⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hA := hu a (Finset.mem_insert_self a s)
    have hB := ih fun b hb => hu b (Finset.mem_insert_of_mem hb)
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hA.1 hB.1, GlobalTheory.MultMem.isCuspFun_add hA.1.toIsAutFun hB.1.toIsAutFun hA.2 hB.2⟩

end GlobalTheory.DnFormApprox

namespace GlobalTheory.DnFormApprox

end GlobalTheory.DnFormApprox

namespace GlobalTheory.DnFormApprox

end GlobalTheory.DnFormApprox
