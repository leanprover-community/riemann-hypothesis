module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleCharacterHyp
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNumericalGaloisDataLocalSituation
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct


theorem _root_.GlobalTheory.T.exists_numerical_galoisData_localSituation : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) (K LL : FinExt l)
    (hA : CaseA K LL) (lam : ↥(OL LL)), Irreducible lam → 5 ≤ (P.PD K).p →
    ∀ (t : ℕ) (h w η : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) (typ : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Bool)
      (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
      (χ : ℕ → ↥(GK K) →* (↥(OL LL))ˣ), tableLineDegreeTwo.TopHyp (P.PD K) (H.W K 1 LL hA.2.2).emb t h w η typ U T.ρ χ →
      (∀ i, Multiset.card (U i) = Module.finrank ↥LL.1 T.V) →
      ∃ (r : ℕ) (D : TopData (Module.finrank ℚ_[l] ↥(K0 K)) r) (ε : ↥(GK K) →* (↥(OL LL))ˣ),
        GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Hyp P K LL (H.W K 1 LL hA.2.2).emb D
          (GalData.mk lam T (χ 1) ε) ∧ D.t = t ∧
        (∀ i a, ((D.Ut i).count a : ℤ) = tableLineDegreeTwo.jTil U w t i a) ∧
        ∀ c ∈ Finset.Icc 1 t,
          (GalData.mk lam T (χ 1) ε : GalData ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)).chi c = χ c := by
  first | exact @GlobalTheory.TopWindow.exists_topData_galData | exact GlobalTheory.TopWindow.exists_topData_galData | (intros; apply GlobalTheory.TopWindow.exists_topData_galData <;> assumption)
