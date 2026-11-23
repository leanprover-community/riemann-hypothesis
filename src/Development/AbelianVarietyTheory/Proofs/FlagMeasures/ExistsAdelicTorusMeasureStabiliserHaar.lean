module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ArchPosHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Assembly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabOrb
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensCnt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensIdxF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolDone
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocPosV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoNuFin
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory

theorem omT_stab_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ a : ℕ, 1 ≤ a → 2 * a < n → ∀ (X0 : Fin a → Fin n → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 → ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure → ∃ (νX : Measure (Fin a → Fin n → AF F ⊗[F] E)) (μ' : Measure (stabT (AF F) σ J X0)), Formalism.L2.SG.Volumes.IsOmT F E σ n J ψ (gramE σ J X0) hT νX ∧ μ'.IsHaarMeasure ∧ Formalism.L2.SG.Volumes.IsCompatT F E σ n J X0 μ μ' νX := by
  intro F E _ _ _ _ _ σ hE n J hJ ha hc ψ hψ a ha1 ha2 X0 hT hdet μ hμ
  obtain ⟨νX, hν⟩ := PI.VolStabS.Assembly.exOmT_holds F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  obtain ⟨μ', hμ'H, hμ'C⟩ := PI.VolStabS.exStab_of_nu PI.VolStabS.Assembly.nuInv_holds
    PI.VolStabS.nuFin_holds
    (PI.VolStabS.nuNeZero_of_dens PI.VolStabS.archPos_holds PI.VolStabS.locPos_holds
      (PI.VolStabS.densAA_of_open PI.VolStabS.volAA_holds PI.VolStabS.hensAA_holds
        PI.VolStabS.idxH_holds PI.VolStabS.cntAA_holds) PI.VolStabS.qvSum_holds)
    F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν
  exact ⟨νX, μ', hν, hμ'H, hμ'C⟩

end GlobalTheory
