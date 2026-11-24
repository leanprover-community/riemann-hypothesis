module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenMulti

theorem multiProd_isSubquotient_of_forall (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} (N : Fin d → ℕ) (M : ℕ) (hM : ∑ i, N i = M)
    (X Y : Fin d → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)]
    (ρ : ∀ i, Representation ℂ (GL (Fin (N i)) k) (X i))
    (ρ' : ∀ i, Representation ℂ (GL (Fin (N i)) k) (Y i))
    (hs : ∀ i, IsSmooth (ρ' i)) (hq : ∀ i, IsSubquotient (ρ i) (ρ' i)) :
    IsSubquotient (multiProd (stdBlocks N hM) ρ) (multiProd (stdBlocks N hM) ρ') :=
  GlobalTheory.ParIndSubquot.parInd_isSubquotient k _ _ _ (GlobalTheory.SmGL.stdBlocks N hM) _ _ _ _
    (GlobalTheory.SmGL.isSmooth_piTensor hs)
    (GlobalTheory.piTensor_isSubquotient_of_forall _ _ X Y ρ ρ' hq)

end GlobalTheory.CompanionTheory.GenMulti
