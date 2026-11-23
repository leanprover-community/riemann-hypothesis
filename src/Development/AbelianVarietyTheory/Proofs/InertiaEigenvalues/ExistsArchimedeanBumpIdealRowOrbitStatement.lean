module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArchimedeanBumpIdealRowOrbit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.exists_archimedeanBump_ideal_rowOrbit : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a)
    (T : Finset (HeightOneSpectrum (𝓞 E))) (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    ∃ (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ 0 < (Φ (Pi.single ℓ 1)).re ∧
      (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) ∧
      ∀ y : Fin a → Af E, y - Pi.single ℓ 1 ∈ GlobalTheory.ThetaPoisson.latt a J →
        ∃ κ ∈ U, (∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ KGL w (n := a)) ∧
          (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
          ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin a) (Fin a) (w.adicCompletion E)) ℓ j = pLoc E w (y j) := by
  first | (exact @GlobalTheory.BumpOrbit.exists_bump_ideal_rowGL) | (exact GlobalTheory.BumpOrbit.exists_bump_ideal_rowGL) | (intros; apply GlobalTheory.BumpOrbit.exists_bump_ideal_rowGL  <;> assumption)
