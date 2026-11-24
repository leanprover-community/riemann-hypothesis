module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirabolicEmbedding
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Coc

theorem continuous_levi_mir (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) : Continuous (levi k n) := by
  have hval : Continuous fun g : GL (Fin n) k => GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k) :=
    GlobalTheory.CompanionTheory.LeibPhi.continuous_glEmbMat_comp n Units.continuous_val
  have hinv : Continuous fun g : GL (Fin n) k =>
      GlobalTheory.BZMir.glEmbMat k n ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) :=
    GlobalTheory.CompanionTheory.LeibPhi.continuous_glEmbMat_comp n Units.continuous_coe_inv
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact hval
  · exact hinv

theorem hgp_cocompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ), ∃ C : Set (Mir k ((i + 1) + t)), IsCompact C ∧
      ∀ g : Mir k ((i + 1) + t), ∃ h ∈ MirabolicParabolic k (i + 1) t, ∃ c ∈ C, g = h * c := by
  intro k _ _ _ _ i t
  refine ⟨GlobalTheory.BZMir.levi k ((i + 1) + t) ''
      (GlobalTheory.SplitWeil.KO k (Fin ((i + 1) + t)) : Set (GL (Fin ((i + 1) + t)) k)),
    GlobalTheory.SplitFlip.isCompact_KO.image (GlobalTheory.CompanionTheory.BZPhiPG.Coc.continuous_levi_mir k _), ?_⟩
  intro g
  obtain ⟨p, w, hw, hx⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul
    (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : (i + 1) + t = (i + 1) + t)))
    (GlobalTheory.BZMir.mirabolicProjection k ((i + 1) + t) g)
  refine ⟨g * (GlobalTheory.BZMir.levi k _ w)⁻¹, ?_, GlobalTheory.BZMir.levi k _ w, ⟨w, hw, rfl⟩,
    (inv_mul_cancel_right g _).symm⟩
  have hmem : ∀ (g : Mir k ((i + 1) + t)),
      g ∈ MirabolicParabolic k (i + 1) t ↔
        mirabolicProjection k ((i + 1) + t) g ∈ parab k (two (stdSum (rfl : (i + 1) + t = (i + 1) + t))) := by
    intro g
    have hlast : ((g : GL (Fin ((i + 1) + t + 1)) k) : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k)
        (Fin.last ((i + 1) + t)) = GlobalTheory.BZMir.eLast k ((i + 1) + t) :=
      (GlobalTheory.BZMir.mem_Mir_iff k (g : GL (Fin ((i + 1) + t + 1)) k)).1 g.2
    have hproj : ∀ a b : Fin ((i + 1) + t),
        ((mirabolicProjection k ((i + 1) + t) g : GL (Fin ((i + 1) + t)) k) : Matrix _ _ k) a b =
          ((g : GL (Fin ((i + 1) + t + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) := fun _ _ => rfl
    simp only [GlobalTheory.BZMir.Leib.MirabolicParabolic, GlobalTheory.BZMir.Leib.eGP, Subgroup.mem_comap,
      Subgroup.coe_subtype, GlobalTheory.SmGL.mem_parab_two, hproj]
    constructor
    · intro h b a
      convert h (Fin.castSucc b) a using 2 <;> apply Fin.ext <;>
        simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]
    · intro h b a
      induction b using Fin.lastCases with
      | last =>
        have h0 : ((g : GL (Fin ((i + 1) + t + 1)) k) : Matrix _ _ k)
            (Fin.last ((i + 1) + t))
            (Fin.castSucc (GlobalTheory.SmGL.stdSum (rfl : (i + 1) + t = (i + 1) + t) (Sum.inl a))) = 0 := by
          rw [hlast]
          simp only [GlobalTheory.BZMir.eLast, Pi.single_apply]
          rw [if_neg (Fin.castSucc_lt_last _).ne]
        convert h0 using 2 <;> apply Fin.ext <;>
          simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]
      | cast b =>
        convert h b a using 2 <;> apply Fin.ext <;>
          simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]
  rw [hmem]
  have hlevi : mirabolicProjection k ((i + 1) + t) (levi k _ w) = w := by
    apply Units.ext
    ext a b
    show GlobalTheory.BZMir.glEmbMat k _ (w : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = _
    simp [GlobalTheory.BZMir.glEmbMat]
  have hproj : GlobalTheory.BZMir.mirabolicProjection k ((i + 1) + t) (g * (GlobalTheory.BZMir.levi k _ w)⁻¹) = p := by
    rw [map_mul, map_inv, hlevi, hx, mul_inv_cancel_right]
  rw [hproj]
  exact p.2

end GlobalTheory.CompanionTheory.BZPhiPG.Coc

end
