module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleCharacterHyp
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.InvariantsVanishing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCycOInvPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopDataOfSlotHyps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInvMultOfIsGenWith
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.TopWindow

theorem exists_topData_galData : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) (K LL : FinExt l)
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
  intro l _ P H K LL hA lam hlam h5 t h w η typ U T χ hyp hc
  have hp : (P.PD K).p = l := P.PD_p K
  have hS : Standing P K LL (H.W K 1 LL hA.2.2).emb lam :=
    (GlobalTheory.SenCompare.standing_iff P H lam).2 ⟨hp ▸ h5, hA, hlam⟩
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hS⟩
  obtain ⟨ht, hposition, -, hcrys, hmult, hchi⟩ := hyp
  rw [hp] at hposition
  obtain ⟨D, hDt, hD, t1, t2, t3⟩ := GlobalTheory.TopWindow.exists_topData_of_positionHyps l _ t _ h w η typ U
    (Fact.out : l.Prime).two_le ht hc hposition
  obtain ⟨-, hcont1, hcrys1, hjump1⟩ := hchi 1 (Finset.mem_Icc.2 ⟨le_rfl, ht⟩)
  have hcyc : ∀ g, tableLineDegreeTwo.charL (LL := ↥LL.1) (GlobalTheory.AdmLoc.CycWitness.cycO P K LL) g =
      Formalism.MainNotions.N.cycLL (P.PD K) ↥LL.1 g := fun g => Units.ext (GlobalTheory.AdmLoc.CycWitness.cycO_val P K LL g)
  refine ⟨_, D, GlobalTheory.AdmLoc.CycWitness.cycO P K LL,
    ⟨hS, ⟨rfl, ⟨hcrys, fun i τ hτ a => ?_⟩, ⟨hcont1, hcrys1, fun i τ hτ a => ?_⟩,
      GlobalTheory.AdmLoc.CycWitness.cycO_val P K LL⟩, t1, t2, t3⟩, hDt, fun i a => (hD i).2.2 a, fun c hc' => ?_⟩
  · rw [(hD i).2.1]
    exact hmult i τ (AlgHom.ext fun x => hτ x) a
  · refine (hjump1 i τ (AlgHom.ext fun x => hτ x) a).trans ?_
    show _ = ((Multiset.count a {D.w i} : ℕ) : ℤ)
    rw [(hD i).1, Multiset.count_singleton]
    push_cast
    simp only [add_sub_cancel_right]
  · obtain ⟨hχc, -⟩ := hchi c hc'
    refine MonoidHom.ext fun g => ?_
    apply Units.map_injective (f := (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom) Subtype.val_injective
    change tableLineDegreeTwo.charL (LL := ↥LL.1) (χ 1 * GlobalTheory.AdmLoc.CycWitness.cycO P K LL ^ (-((c : ℤ) - 1))) g =
      tableLineDegreeTwo.charL (LL := ↥LL.1) (χ c) g
    rw [hχc g, ← hcyc g]
    simp [tableLineDegreeTwo.charL, map_zpow]

end GlobalTheory.TopWindow
