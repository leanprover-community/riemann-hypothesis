module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousCyclotomicCharacterPeriodDatumStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsJumpVOfMultVNeZero
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

theorem tateDual_matRep_crys : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {k : ℕ} (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1), (∀ (A A' : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (Pr : A.V →ₗ[↥LL.1] A'.V →ₗ[↥LL.1] ↥LL.1), IsDual1 (P.PD K) A.ρ A'.ρ Pr → IsCrys (P.PD K) A.ρ → IsCrys (P.PD K) A'.ρ) → Continuous M → IsCrys (P.PD K) (matRep M) → Continuous (twistM (dualM M) (cycLL (P.PD K) ↥LL.1)) ∧ IsCrys (P.PD K) (matRep (twistM (dualM M) (cycLL (P.PD K) ↥LL.1))) := by
  intro l _ P K LL k M hT hM hC
  haveI : IsTopologicalRing ↥LL.1 := by
    first
      | infer_instance
      | exact Subring.instIsTopologicalRing LL.1.toSubring
      | exact inferInstanceAs (IsTopologicalRing ↥LL.1.toSubfield.toSubring)
  have hχ := GlobalTheory.T.continuous_cyclotomicCharacter_periodDatum P K LL
  have hinv : Continuous fun g : ↥(GK K) => M g⁻¹ := hM.comp continuous_inv
  have hc : Continuous (twistM (dualM M) (cycLL (P.PD K) ↥LL.1)) := by
    change Continuous fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) • (M g⁻¹).transpose
    exact hχ.smul hinv.matrix_transpose
  refine ⟨hc, ?_⟩
  exact hT (TwistDualLoc.matGRep ℚ_[l] ↥(OL LL) M hM)
    (TwistDualLoc.matGRep ℚ_[l] ↥(OL LL) _ hc) (dotProductBilin ↥LL.1 ↥LL.1)
    (TwistDualLoc.isDual1_dot (P.PD K) M) hC

end GlobalTheory.HTW.Rec
