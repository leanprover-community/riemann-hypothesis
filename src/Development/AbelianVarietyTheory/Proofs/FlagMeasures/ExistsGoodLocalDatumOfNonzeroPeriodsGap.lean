module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapPairingBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFdegSmulOfIsDS
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.KStableFiniteDimSmoothCompactRootStable
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DatumOfPeriodsGap

theorem exists_goodS : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (R : Rep D.R.k D.R.rS) (h : ℝ) (l : R.H → W.Wp) (l' : R.H → W.Wq) (dd : ℝ), cdScaleTie D → GoodW D τ w w' θ W → R.IsDG (epsSH D.R) lam → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) R.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') R.σ W.π' l' → 0 < dd → (∀ v ∈ R.sm, l2SG W.νS (fun g => l (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → (∀ v ∈ R.sm, l2SG W.νS' (fun g => l' (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → ∃ A : LocS W, GoodS D lam A := by
  intro hH D τ w w' θ W lam R _ l l' dd _ _ hRG hl hl' hdd hn hn'
  have hK : PI.KFinSmooth := hH.1.1.2.2.1
  have hR : R.IsDS (epsSH D.R) lam := GlobalTheory.isDS_of_isDG hRG
  obtain ⟨P, hP, hD⟩ := hR.2
  have hD' : Formalism.MainNotions.S.IsDS (epsSH D.R) lam (fun g => R.σ (P⁻¹ * g * P)) := hD
  obtain ⟨d, hd⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS _ _ _ _ _ hD' _ (D.s.cdScale_pos _ (epsSH D.R))
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hD'
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  have hvs : v ∈ R.sm :=
    ((GlobalTheory.CompactStable.kStable_smooth_and_stable hK _ _ _ lam R hR P hP S hS.1 hS.2.1).1 v hvS).2
  refine ⟨{ H := R.H, σ := R.σ, B := fun x => ((Real.sqrt (Module.finrank ℂ W.Wp : ℕ) : ℝ) : ℂ) • l x,
            B' := fun x => ((Real.sqrt (Module.finrank ℂ W.Wq : ℕ) : ℝ) : ℂ) • l' x,
            v0 := v, cN := ‖v‖ ^ 2 / dd, deg := d },
    hR.1, hR.2, GlobalTheory.DatumOfPeriods.isBesselMapSm_smul hl _, GlobalTheory.DatumOfPeriods.isBesselMapSm_smul hl' _, hvs, hv0,
    ⟨P, hP, ?_⟩, div_pos (pow_pos (norm_pos_iff.2 hv0) 2) hdd,
    GlobalTheory.DatumOfPeriods.l2SG_sqrt_smul_eq_ofReal_mul _ _ _ _ (hn v hvs), GlobalTheory.DatumOfPeriods.l2SG_sqrt_smul_eq_ofReal_mul _ _ _ _ (hn' v hvs),
    P, hP.1, hd⟩
  exact (le_sSup (s := {S | IsKTypeOf (epsSH D.R) (fun g => R.σ (P⁻¹ * g * P)) (Formalism.QuantumDeterminants.lowK (epsSH D.R) lam) S}) hS) hvS

end GlobalTheory.DatumOfPeriodsGap
