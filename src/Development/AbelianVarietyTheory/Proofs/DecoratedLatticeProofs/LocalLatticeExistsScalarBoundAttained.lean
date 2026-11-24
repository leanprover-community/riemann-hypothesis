module

public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.LocalField.Basic
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

namespace GlobalTheory

theorem lattice_exists_scalar_bound_attained : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (L : Submodule 𝒪[k] (n → k)), L.IsFullLattice k → Nonempty n → ∃ c : k, c ≠ 0 ∧ (∀ x ∈ L, ∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ x ∈ L, ∃ j, x j = c := by
  intro k _ _ _ _ n _ L hL hn
  obtain ⟨s, hs⟩ := hL.fg

  have hex : ∃ x ∈ s, ∃ j, x j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hbot : L = ⊥ := by
      rw [← hs, Submodule.span_eq_bot]
      intro x hx
      funext j
      exact hcon x hx j
    have htop := hL.span_eq_top
    rw [hbot] at htop
    simp only [Submodule.bot_coe, Submodule.span_zero_singleton] at htop
    obtain ⟨j⟩ := hn
    have h1 : (Pi.single j (1 : k) : n → k) ∈ (⊤ : Submodule k (n → k)) := Submodule.mem_top
    rw [← htop, Submodule.mem_bot] at h1
    have := congrFun h1 j
    simp at this
  obtain ⟨x0, hx0, j0, hx0j⟩ := hex
  have hne : (s ×ˢ (Finset.univ : Finset n)).Nonempty := ⟨(x0, j0), by simp [hx0]⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (s ×ˢ (Finset.univ : Finset n))
    (fun q : (n → k) × n => valuation k (q.1 q.2)) hne
  have hc : p.1 p.2 ≠ 0 := by
    intro h0
    have := hmax (x0, j0) (by simp [hx0])
    simp only [h0, map_zero] at this
    have h' : valuation k (x0 j0) = 0 := le_antisymm this zero_le'
    exact hx0j ((Valuation.zero_iff _).mp h')
  refine ⟨p.1 p.2, hc, ?_, p.1, ?_, p.2, rfl⟩
  · intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      intro j
      show valuation k ((p.1 p.2)⁻¹ * y j) ≤ 1
      have hle := hmax (y, j) (by simpa using hy)
      simp only at hle
      have hvc : valuation k (p.1 p.2) ≠ 0 := by simpa using hc
      rw [map_mul, map_inv₀]
      calc (valuation k (p.1 p.2))⁻¹ * valuation k (y j)
          ≤ (valuation k (p.1 p.2))⁻¹ * valuation k (p.1 p.2) := by gcongr
        _ = 1 := inv_mul_cancel₀ hvc
    | zero => intro j; simp
    | add y z _ _ hy hz =>
      intro j
      simpa [mul_add] using add_mem (hy j) (hz j)
    | smul a y _ hy =>
      intro j
      have := mul_mem a.2 (hy j)
      convert this using 1
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      ring
  · rw [← hs]
    exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_product.mp hp).1)

end GlobalTheory
