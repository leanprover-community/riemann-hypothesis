module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTupleGramDetNeZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExOmTOfSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibDis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibre

theorem dX_dT_omFam :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, 1 ≤ a → 2 * a < n → (Formalism.L2.SG.LocVol.dX σ J ψ v a).IsAddHaarMeasure ∧ (Formalism.L2.SG.LocVol.dT σ ψ v a).IsAddHaarMeasure ∧ Formalism.L2.SG.LocVol.IsOm σ J ψ v a (Formalism.L2.SG.LocVol.omFam σ J ψ v a) := by
  intro F E _ _ _ _ _ σ hE n J hJ ha hc ψ hψ v a ha1 ha2
  obtain ⟨X0, hdet, hT⟩ := GlobalTheory.NondegTuple.exists_tuple_gram_det_ne_zero F E σ hE n J hJ a (by omega)
  have hI : PI.VolStabS.FibInfEx :=
    PI.VolStabS.fibInfEx_of PI.VolStabS.DiscreteGroups.fibOfDens_holds PI.VolStabS.tensAll_holds
      PI.VolStabS.densInf_holds
  have hV : PI.VolStabS.FibVEx :=
    PI.VolStabS.fibVEx_of PI.VolStabS.DiscreteGroups.fibOfDens_holds PI.VolStabS.tensAll_holds
      PI.VolStabS.densV_holds
  obtain ⟨_, _, μv, νv, _, _, _, _, hμv, hνv, _, _⟩ :=
    PI.VolStabS.locEx_of hI hV PI.VolStabS.latSB_holds F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet
      ψ hψ
  have hX : ∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ := ⟨_, hμv v⟩
  have hH : ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν := ⟨_, hνv v⟩
  have hdX : SdW F E σ n J (Fv F v) (psiV F ψ v) a (Formalism.L2.SG.LocVol.dX σ J ψ v a) := by
    unfold Formalism.L2.SG.LocVol.dX
    rw [dite_eq_left hX]
    exact hX.choose_spec
  have hdT : SdHerm F E σ (Fv F v) (psiV F ψ v) a (Formalism.L2.SG.LocVol.dT σ ψ v a) := by
    unfold Formalism.L2.SG.LocVol.dT
    rw [dite_eq_left hH]
    exact hH.choose_spec
  have hO : ∃ fib, Formalism.L2.SG.LocVol.IsOm σ J ψ v a fib :=
    hV F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v _ hdX _ hdT
  refine ⟨hdX.1, hdT.1, ?_⟩
  unfold Formalism.L2.SG.LocVol.omFam
  rw [dite_eq_left hO]
  exact hO.choose_spec

end GlobalTheory.LocalFibre
