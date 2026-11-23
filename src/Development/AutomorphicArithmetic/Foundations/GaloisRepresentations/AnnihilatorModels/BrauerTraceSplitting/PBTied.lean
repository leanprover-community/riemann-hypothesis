module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.AwayEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.LocFacts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.LocTied6
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.TiedAInvOfTheta
import GroundTheory.PAdicHodge.ACrisPhi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison GroundTheory.PAdicHodge

namespace UpperTheory.Gal.crystallineComparison.Br

variable {l : ℕ} [Fact l.Prime]

private theorem l_dvd : ∃ r : ℕ, (l : Acris l) ∣ tA l ^ r := by
  exact ⟨l - 1, Ideal.mem_span_singleton.mp
    (ACris.periodT_pow_mem' (K := ℂ_[l]) (p := l) (untilt_epsilon (p := l)))⟩

private def cT {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) : Acris l →+* P.R.B :=
  T.eB.symm.toRingHom.comp (Formalism.Per6.cB l)

private theorem eB_cT {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (a : Acris l) :
    T.eB (cT T a) = Formalism.Per6.cB l a :=
  T.eB.apply_symm_apply _

private theorem cT_unit {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) : IsUnit (cT T (tA l)) := by
  have ht : IsUnit (Formalism.Per6.cB l (tA l)) :=
    (PositivityTheory.LocInh.cB_isFrac l).2.1
  exact ht.map T.eB.symm

private theorem transport_locFacts {A C : Type} [CommRing A] [CommRing C] {a t : A}
    (hdiv : ∃ r : ℕ, a ∣ t ^ r) (c : A →+* C) (e : C ≃+* Formalism.Per6.Loc2 a t)
    (hc : ∀ y, e (c y) = Formalism.Per6.Loc2.mk₀ a t y) :
    (∀ x : C, ∃ (r : ℕ) (y : A), c t ^ r * x = c y) ∧
    (∀ y : A, c y = 0 → ∃ r : ℕ, t ^ r * y = 0) := by
  obtain ⟨hloc, hker⟩ := locFacts A a t hdiv
  constructor
  · intro x
    obtain ⟨r, y, hy⟩ := hloc (e x)
    refine ⟨r, y, e.injective ?_⟩
    simp only [map_mul, map_pow, hc]
    exact hy
  · intro y hy
    exact hker y ((hc y).symm.trans ((congrArg e hy).trans e.map_zero))

private theorem cT_locFacts {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) :
    (∀ x : P.R.B, ∃ (r : ℕ) (a : Acris l), cT T (tA l) ^ r * x = cT T a) ∧
    (∀ a : Acris l, cT T a = 0 → ∃ r : ℕ, tA l ^ r * a = 0) :=
  transport_locFacts (a := (l : Acris l)) (t := tA l) l_dvd (cT T) T.eB (eB_cT T)

private theorem cT_loc {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (x : P.R.B) :
    ∃ (r : ℕ) (a : Acris l), cT T (tA l) ^ r * x = cT T a :=
  (cT_locFacts T).1 x

private theorem cT_ker {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (a : Acris l)
    (h : cT T a = 0) : ∃ r : ℕ, tA l ^ r * a = 0 :=
  (cT_locFacts T).2 a h

private theorem cT_φ {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (a : Acris l) :
    P.φB (cT T a) = cT T (phiA l a) := by
  refine T.eB.injective ?_
  rw [T.frob, eB_cT, eB_cT]
  exact PositivityTheory.LocInh.φB_cB a

private theorem cT_σ {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI)
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (g : K.fixingSubgroup) (a : Acris l) :
    P.actQ g.1 (cT T a) = cT T (galA g a) := by
  refine T.eB.injective ?_
  rw [T.actB, eB_cT, eB_cT, ((actEq l).1 K g a)]
  exact PositivityTheory.LocInh.σB_cB _ a

private theorem algebraMap_padic_int_eq_period {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (x : ℤ_[l]) :
    algebraMap ℚ_[l] P.R.B (x : ℚ_[l]) = cT T (zA l x) := by
  refine T.eB.injective ?_
  rw [T.zB, eB_cT]
  exact (actEq l).2 x

private def pullbackToFiniteExtension {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (K : FinExt l) : PB l K.1 where
  C := P.R.B
  c := cT T
  φ := P.φB
  σ g := (P.actQ g.1).toAlgHom
  t_unit := cT_unit T
  loc := cT_loc T
  ker := cT_ker T
  φ_c := cT_φ T
  σ_c := cT_σ T K.1
  z_c := algebraMap_padic_int_eq_period T

theorem pBTied : PBTied := by
  intro l _ P AI hT K
  exact (UpperTheory.Lit.Cmp.locTied6 l P AI hT).elim fun T =>
    ⟨pullbackToFiniteExtension T K, AlgEquiv.refl, fun _ _ => rfl, fun _ => rfl, PositivityTheory.LocInh.tiedA_φ_injective P⟩

end UpperTheory.Gal.crystallineComparison.Br
