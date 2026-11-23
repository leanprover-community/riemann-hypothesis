module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdGalSubStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinBasisOfSemistablePeriodsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameIsDeRhamStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsBreuilKisinGaloisStableStatement
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem semistablePeriodFrame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ), ∃ (N : ℕ) (F : Frame bk N d ρ), F.IsDR ∧ ((∀ g, s.κ g = 1) → F.IsCr) := by
  intro l _ K bk τ hτ d ρ hρ s
  obtain ⟨N, F, Y, Z, hY, hZ, hW⟩ := GlobalTheory.T.exists_breuilKisinBasis_of_semistablePeriods l K bk τ hτ d ρ hρ s
  obtain ⟨F₀, rfl, hε⟩ := GlobalTheory.T.semistablePeriods_breuilKisin_galoisStable l K bk τ hτ d ρ hρ s N F Y Z hY hZ hW
  refine ⟨N, F₀, ?_, ?_⟩
  · exact GlobalTheory.T.semistablePeriodFrame_isDeRham l K bk τ hτ d ρ hρ s N F₀ Y Z hY hZ hW hε
  · intro hκ
    exact GlobalTheory.T.isCr_of_wSeed_alt l K bk τ hτ d ρ hρ s N F₀ Y Z hY hZ hW hε hκ

end GlobalTheory
