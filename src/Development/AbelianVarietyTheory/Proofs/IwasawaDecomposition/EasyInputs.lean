module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DimKKapAtWcPos
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Formalism.LocalRingCardinality.PosOfIsomEmb
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.EasyInputs

theorem smAll (D : D7) : SmAll D := fun V S M τ => by
  obtain ⟨w, hw, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)
  exact ⟨⟨w, hw⟩, by simpa using h0⟩

theorem dimOK (D : D7) : DimOK D := fun i σ ρ => GlobalTheory.Mem.WeylDimPos.dimK_kapAt_Wc_pos D i σ ρ

theorem cartanOK (D : D7) : CartanOK D := by
  refine ⟨fun V S M _ τ => GlobalTheory.Chain.VacVec.cart_isCartanInv M τ, fun V hs hp τ => ?_⟩
  have h := GlobalTheory.RepsObj.gramAt_posDef hp hs τ
  exact ⟨by simp, by simp, by simpa using h⟩

theorem spOK (D : D7) : SpOK D := by
  refine ⟨fun τ => Or.inl ?_, fun τ => Or.inl (D.X'_posDef τ)⟩
  have hm : D.R.m - 1 ≤ D.R.m := Nat.sub_le _ _
  show (D.sp.Y (min (D.R.m - 1) D.R.m)).sig τ = ((D.sp.Y (min (D.R.m - 1) D.R.m)).rank, 0)
  rw [min_eq_left hm, D.Y_sigval _ hm τ, D.sp.Y_rank _ hm, sigYD]
  have := D.R.two_le_m
  have h1 : (D.R.m - (D.R.m - 1)) / 2 = 0 := by omega
  rw [h1, Nat.sub_zero]

theorem selfDualOK (D : D7) : SelfDualOK D := by
  rintro V β Λ N ⟨-, hd, hN, h1, h2⟩
  have hM0 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hL := (GlobalTheory.PlaceModel.isSelfDualC_latFrame V).1
  rw [← GlobalTheory.PlaceModel.coe_latFrame] at h1 h2
  refine ⟨⟨?_, ?_⟩, fun y => ?_⟩
  · let f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
      (LinearMap.lsmul D.host.E (Fin V.rank → D.host.E) (N : D.host.E)⁻¹).restrictScalars (𝓞 D.host.E)
    refine (hL.fg.map f).of_le fun x hx => ⟨_, h2 x hx, ?_⟩
    change (N : D.host.E)⁻¹ • ((N : D.host.E) • x) = x
    rw [smul_smul, inv_mul_cancel₀ hM0, one_smul]
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · rw [← GlobalTheory.SDFrameLattice.mem_dualL_iff, hd]


open scoped Pointwise in
theorem petAll (D : D7) : PetAll D := by
  intro V μ 𝓕 hμ h𝓕 F hc hl h0 hi
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun g => by positivity) hi]
  have hs : Function.support (fun g => ‖F g‖ ^ 2) = Function.support F := by
    ext g
    simp [Function.mem_support]
  rw [hs, pos_iff_ne_zero]
  intro hz
  have hinv : ∀ γ : GQ V, γ • Function.support F = Function.support F := fun γ => by
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem, Function.mem_support, Function.mem_support]
    have : F (γ⁻¹ • g) = F g := hl _ (γ⁻¹).2 g
    rw [this]
  have hzero := h𝓕.measure_zero_of_invariant _ hinv hz
  exact (hc.isOpen_support.measure_pos μ (Function.support_nonempty_iff.2 h0)).ne' hzero

theorem easy_inputs : ∀ D : D7, CartanOK D ∧ SelfDualOK D ∧ SpOK D ∧ DimOK D ∧ PetAll D ∧ SmAll D := fun D =>
  ⟨cartanOK D, selfDualOK D, spOK D, dimOK D, petAll D, smAll D⟩

end GlobalTheory.Mem.EasyInputs
