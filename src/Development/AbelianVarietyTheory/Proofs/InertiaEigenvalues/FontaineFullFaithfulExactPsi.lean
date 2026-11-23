module

public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleFunctorExactOnLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingFreeOverFrobeniusImageStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiOperatorEtalePhiGammaModuleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorFullyFaithfulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorRingPsiOperatorExistsOfGoodStatement
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

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem fontaine_litFont_assembled :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.InvariantsGenerators.LitFont D HW F := by
  intro D HW F
  unfold Formalism.MainNotions.InvariantsGenerators.LitFont
  intro l _ K LL hA
  unfold Formalism.MainNotions.InvariantsGenerators.FontCore
  have hff := GlobalTheory.T.wachFunctor_fullyFaithful D HW F l K 1 LL hA.2.2
  have hex := GlobalTheory.T.etaleFunctor_exact_on_lattices D HW F l K 1 LL hA.2.2
  have hpd := GlobalTheory.T.exists_psi_operator_etale_phiGamma_module D HW F l K 1 LL hA.2.2
  have hpe := GlobalTheory.T.wachFunctorRing_psiOperator_exists_of_good D HW F l K 1 LL hA.2.2
  have hfr := GlobalTheory.T.etaleRing_free_over_frobenius_image D HW F l K 1 LL hA.2.2
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨hff, hex, ?_, hpd⟩
  obtain ⟨ψ, h1, h2, h3⟩ := hpe
  refine ⟨ψ, h1, h2, ?_, ?_⟩
  · rw [hp]; exact h3
  · intro x
    obtain ⟨c, hc, -⟩ := hfr x
    rw [hp]
    exact ⟨c, hc⟩

end GlobalTheory
