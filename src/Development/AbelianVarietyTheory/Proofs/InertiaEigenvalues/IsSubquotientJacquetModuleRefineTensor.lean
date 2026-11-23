module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientRelativeJacquetBlockLeviStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetModuleInStagesRefinedBlocksStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PiExteriorTensorFlattenedIndexEquivNestedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeJacquetPiExteriorTensorEquivNormalizedStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiExteriorTensorIsSubquotientOfForall
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientOfEquiv

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open GlobalTheory.JacStages

namespace GlobalTheory.JacStages

theorem isSubquotient_jac_refine : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    ∀ (X : Fin s → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (ρ a)) →
    IsSubquotient (piTensor ρ) (jac e π) →
    ∀ (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)]
    (ρ' : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (Y a b)),
    (∀ a, IsSubquotient (piTensor (ρ' a)) (jac (e' a) (ρ a))) →
    ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n,
      IsSubquotient (piTensor fun c => ρ' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) (jac E π) := by
  intro k _ _ _ _ n s d e V _ _ π hπ X _ _ ρ _ hsub t d' e' Y _ _ ρ' hρ'
  refine ⟨refinePlace e e', ?_⟩
  refine isSubquotient_of_comp (flatHom fun a b => GL (Fin (d' a b)) k) (flatHom_surjective _) ?_
  obtain ⟨φR⟩ := GlobalTheory.T.piExteriorTensor_flattenedIndex_equiv_nested s t (fun a b => GL (Fin (d' a b)) k) Y ρ'
  obtain ⟨φT⟩ := GlobalTheory.T.relativeJacquet_piExteriorTensor_equiv_normalized k s d t d' e' X ρ
  obtain ⟨φS⟩ := GlobalTheory.T.jacquetModule_in_stages_refined_blocks k s n d e t d' e' V π
  have h1 : IsSubquotient (piTensor fun a => piTensor (ρ' a)) (piTensor fun a => jac (e' a) (ρ a)) :=
    GlobalTheory.piTensor_isSubquotient_of_forall _ _ _ _ _ _ hρ'
  have h3 := GlobalTheory.T.isSubquotient_relativeJacquet_blockLevi k s d t d' e' _ _ (piTensor ρ) (jac e π) (isSmooth_jac e hπ) hsub
  exact (isSubquotient_of_equiv φR).trans (h1.trans ((isSubquotient_of_equiv φT.symm).trans
    (h3.trans (isSubquotient_of_equiv φS.symm))))

end GlobalTheory.JacStages
