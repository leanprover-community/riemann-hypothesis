module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TameLiftResidueCharacterIsTameNotUnramified
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
noncomputable section

namespace GlobalTheory.NormIdealUnit

theorem unit_at_split_place : ∀ (D : D7) (PP : Pl D.host.E), ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → ∀ (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ((∃ a : D.host.E, a ∈ D.host.AA ∧ Valued.v (rdQ φ a) = 1) ∧ ∀ a : D.host.E, a ∈ D.host.AA → Valued.v (rdQ φ a) ≤ 1) := by
  intro D PP hPP v φ hφ
  have hq : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun h => hPP (by
    rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun h => hPP (by
    rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
  have unit : ∀ x : 𝓞 D.host.E, x ∉ PP.asIdeal → Valued.v (rdQ φ (x : D.host.E)) = 1 := fun x hx =>
    le_antisymm (GlobalTheory.TameLiftChar.val_rdQ_le_one φ x) (not_lt.1 fun h => hx ((hφ x).2 h))
  refine ⟨⟨_, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D, ?_⟩, ?_⟩
  · have := unit _ hN
    simpa using this
  · have hnot : ¬ D.host.𝔟 ≤ PP.asIdeal :=
      haveI := PP.isPrime; UpperTheory.Ram.half_not_le D.host _ hq
    obtain ⟨z, hz, hzP⟩ := Set.not_subset.1 hnot
    have hz1 := unit z hzP
    have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.2 (Formalism.L2.Pj.b_ne_bot D)
    have hAA0 : ∀ a : D.host.E, a ∈ D.host.AA0 → Valued.v (rdQ φ a) ≤ 1 := by
      intro a ha
      unfold Host.AA0 at ha
      rw [FractionalIdeal.mem_inv_iff hB] at ha
      obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1 (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩))
      have h3 := GlobalTheory.TameLiftChar.val_rdQ_le_one φ w
      rw [RingOfIntegers.coe_eq_algebraMap, hw, ← GlobalTheory.TameLiftChar.rdQHom_apply, map_mul, map_mul,
        GlobalTheory.TameLiftChar.rdQHom_apply, GlobalTheory.TameLiftChar.rdQHom_apply] at h3
      rw [← RingOfIntegers.coe_eq_algebraMap] at h3
      rw [hz1] at h3
      simpa using h3
    have hle : D.host.AA ≤ D.host.AA0 := by
      unfold Host.AA
      calc (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0
          ≤ 1 * D.host.AA0 := by first | exact FractionalIdeal.mul_right_mono _ FractionalIdeal.coeIdeal_le_one | exact mul_le_mul_left FractionalIdeal.coeIdeal_le_one _ | gcongr; exact FractionalIdeal.coeIdeal_le_one
        _ = D.host.AA0 := one_mul _
    exact fun a ha => hAA0 a (hle ha)

end GlobalTheory.NormIdealUnit
