module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem GlobalTheory.ChangeEtaleBasis.main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (T0 Wm Wm' A0 A0' : Matrix (Fin d) (Fin d) (WCb l)), (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T0.map (galW l (g : GQ l)) = T0) → (∀ i j, A0 i j ∈ bk.OE) → (∀ i j, A0' i j ∈ bk.OE) → T0.map (frobW l) = T0 * A0 → A0 * A0' = 1 → (∀ i j, Wm i j ∈ bk.OE) → (∀ i j, Wm' i j ∈ bk.OE) → Wm * Wm' = 1 → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * (T0 * Wm).map (galW l (g : GQ l)) = T0 * Wm) ∧ ∃ A1 A1' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A1 i j ∈ bk.OE) ∧ (∀ i j, A1' i j ∈ bk.OE) ∧ (T0 * Wm).map (frobW l) = (T0 * Wm) * A1 ∧ A1 * A1' = 1 := by
  intro l _ K bk d ρ T0 Wm Wm' A0 A0' hT0 hA0 hA0' hfr hAA hW hW' hWW
  have hO := GlobalTheory.T.integral_elements_unit_factorization l K bk
  have hgal : ∀ g : ↥(GK K), bk.FixFlat g → Wm.map (galW l (g : GQ l)) = Wm := by
    intro g hg
    exact Matrix.ext fun i j => by
      simp only [Matrix.map_apply]
      exact hO.2.2.2.2.2.1 g hg _ (hW i j)
  have hfrob : ∀ M : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, M i j ∈ bk.OE) → ∀ i j, M.map (frobW l) i j ∈ bk.OE := by
    intro M hM i j
    exact hO.2.2.2.2.2.2 _ (hM i j)
  have hmul : ∀ M N : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, M i j ∈ bk.OE) → (∀ i j, N i j ∈ bk.OE) → ∀ i j, (M * N) i j ∈ bk.OE := by
    intro M N hM hN i j
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ (fun k _ => Subring.mul_mem _ (hM i k) (hN k j))
  have hW'W : Wm' * Wm = 1 := mul_eq_one_comm.mp hWW
  refine ⟨?_, Wm' * A0 * Wm.map (frobW l), Wm'.map (frobW l) * A0' * Wm, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have hmap : (T0 * Wm).map (galW l (g : GQ l)) = T0.map (galW l (g : GQ l)) * Wm.map (galW l (g : GQ l)) :=
      Matrix.map_mul (f := ((galW l (g : GQ l)) : WCb l →+* WCb l))
    rw [hmap, hgal g hg, ← Matrix.mul_assoc, hT0 g hg]
  · exact hmul _ _ (hmul _ _ hW' hA0) (hfrob _ hW)
  · exact hmul _ _ (hmul _ _ (hfrob _ hW') hA0') hW
  · have hmap : (T0 * Wm).map (frobW l) = T0.map (frobW l) * Wm.map (frobW l) :=
      Matrix.map_mul (f := ((frobW l) : WCb l →+* WCb l))
    rw [hmap, hfr]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wm Wm', hWW, Matrix.one_mul]
  · have hφ : Wm.map (frobW l) * Wm'.map (frobW l) = 1 := by
      have e : (Wm * Wm').map (frobW l) = Wm.map (frobW l) * Wm'.map (frobW l) :=
        Matrix.map_mul (f := ((frobW l) : WCb l →+* WCb l))
      rw [← e, hWW]; exact Matrix.map_one _ (map_zero _) (map_one _)
    calc Wm' * A0 * Wm.map (frobW l) * (Wm'.map (frobW l) * A0' * Wm)
        = Wm' * A0 * (Wm.map (frobW l) * Wm'.map (frobW l)) * A0' * Wm := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hφ, Matrix.mul_one, Matrix.mul_assoc Wm', hAA, Matrix.mul_one, hW'W]
