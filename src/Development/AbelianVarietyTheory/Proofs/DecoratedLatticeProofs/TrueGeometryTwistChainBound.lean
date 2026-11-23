module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevSph

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

namespace GlobalTheory.TopVol.InKConj

variable {D : D7}

theorem idAt_le_of {P : Pl D → Prop} {v : Pl D} (hv : P v) : idAt D (· = v) ≤ idAt D P := by
  intro a ha
  rw [idAt, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun h => w.2 (h ▸ hv)⟩⟩

theorem moves_at {V : HSp D} {g : GA D V} {M : Lat V} {P : Pl D → Prop} (h : Moves V g M M P) {v : Pl D} (hv : P v) :
    Moves V g M M (· = v) := by
  intro y hy
  have hy' : ∀ i, y i ∈ idAt D P := fun i => idAt_le_of hv (hy i)
  rw [KOpen.mem_latV_iff V M _ y hy, KOpen.mem_latV_iff V M _ _ (KOpen.supp_mulVec V _ g hy),
    ← KOpen.mem_latV_iff V M P y hy', ← KOpen.mem_latV_iff V M P _ (KOpen.supp_mulVec V P g hy')]
  exact h y hy'

theorem conj_mem_levG (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ M : Lat V) (Ld : LevDat D.host.E ℂ V.rank)
    (P : Pl D → Prop) (t κ : GA D V) (hβ : IsFrame β Λ) (hΛ : IsSelfDualC V Λ) (ht : t ∈ GfC V)
    (hm : ∀ v, P v → Moves V t Λ M (· = v)) (hQ : Ld.Q = ∅)
    (hPg : ∀ PP ∈ Ld.Pg, ¬ P ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) (hκ : InK V M P κ) :
    t⁻¹ * κ * t ∈ Lev.levG V β Ld := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hfg : Λ.FG := Submodule.IsLattice.fg (A := D.host.E) Λ
  obtain ⟨hκf, hκ1⟩ := (KOpen.mem_grpAt_iff V P κ).1 hκ.1
  have hy : t⁻¹ * κ * t ∈ GfC V := (GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem ht) hκf) ht
  have hproj : ∀ v, ¬ P v → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (t⁻¹ * κ * t) = 1 := fun v hv => by
    rw [map_mul, map_mul, hκ1 v hv, mul_one, map_inv, inv_mul_cancel]
  have hSt : Lev.finE V (t⁻¹ * κ * t) ∈ St β := by
    rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ]
    intro v
    by_cases hv : P v
    · rw [← GlobalTheory.StMoves.moves_iff_stabLoc V Λ hfg v]
      exact (GlobalTheory.StMoves.moves_conj_iff κ (hm v hv)).2 (moves_at hκ.2 hv)
    · rw [hproj v hv]; exact Subgroup.one_mem _
  have hred : ∀ PP ∈ Ld.Pg, redFn β PP (Lev.finE V (t⁻¹ * κ * t)) = 1 := fun PP hP =>
    GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP hSt (hproj _ (hPg PP hP))
  refine ⟨hy, mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hSt, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩⟩
  · rw [hred PP hP]; exact Subgroup.one_mem _
  · rw [hQ] at hP; exact absurd hP (Finset.notMem_empty _)
  · have e : rTup β Ld (Lev.finE V (t⁻¹ * κ * t)) = 1 := by
      funext PP
      show upperLeftBlock Ld.hr (redFn β PP.1 _) = 1
      rw [hred PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
    rw [e]; exact Subgroup.one_mem _

end GlobalTheory.TopVol.InKConj

namespace GlobalTheory.TopVol.InKConj

end GlobalTheory.TopVol.InKConj
