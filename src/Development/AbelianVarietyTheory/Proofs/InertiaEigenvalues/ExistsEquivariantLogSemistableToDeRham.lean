module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogTiltKummerCoboundaryBdRStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BstLog

theorem iota_exists : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ ι : Bst P →ₐ[ℚ_[l]] P.R.BdR, (∀ b, ι (Polynomial.C b) = P.ιB b) ∧
      (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) := by
  intro l _ P AI T
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_log_tilt_kummerCoboundary_BdR l P AI T
  have hcomm : ∀ (g : GQ l) (z : P.R.B), P.ιB (P.actQ g z) = P.actQdR g (P.ιB z) := by
    intro g z
    have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ z
    rwa [P.PD_ι, P.PD_actB, P.PD_ι, P.PD_actdR] at this
  let ι : Bst P →ₐ[ℚ_[l]] P.R.BdR := Polynomial.eval₂AlgHom P.ιB u (fun _ => Commute.all _ _)
  refine ⟨ι, fun b => Polynomial.eval₂_C _ _, fun g x => ?_⟩
  have h : ι.comp (actSt P g) = ((P.actQdR g : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →ₐ[ℚ_[l]] P.R.BdR).comp ι := by
    apply Polynomial.algHom_ext'
    · ext b
      show Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (actSt P g (Polynomial.C b)) =
        P.actQdR g (Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (Polynomial.C b))
      rw [actSt_C, Polynomial.eval₂_C, Polynomial.eval₂_C]
      exact hcomm g b
    · show Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (actSt P g Polynomial.X) =
        P.actQdR g (Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u Polynomial.X)
      rw [actSt_X, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, hu]
      rfl
  exact congrArg (fun F : Bst P →ₐ[ℚ_[l]] P.R.BdR => F x) h

end GlobalTheory.BstLog
