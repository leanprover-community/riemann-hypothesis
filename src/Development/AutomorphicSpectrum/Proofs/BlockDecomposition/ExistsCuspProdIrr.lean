module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSubquotientExtTensorRight
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.Ysupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSubquotient_of_prod₂_equiv {r t : ℕ} {U W A B C D : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    [AddCommGroup D] [Module ℂ D] {σ : Representation ℂ (GL (Fin r) k) U} {ρ : Representation ℂ (GL (Fin t) k) W}
    {α : Representation ℂ (GL (Fin r) k) A} {β : Representation ℂ (GL (Fin t) k) B}
    {γ : Representation ℂ (GL (Fin (r + t)) k) C} {δ : Representation ℂ (GL (Fin (r + t)) k) D}
    (hα : IsSmooth α) (hβ : IsSmooth β) (h₁ : IsSubquotient σ α) (h₂ : IsSubquotient ρ β)
    (E : (prod₂ σ ρ).Equiv δ) (F : (prod₂ α β).Equiv γ) : IsSubquotient δ γ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.toLinearEquiv.surjective).trans
    ((GlobalTheory.CompanionTheory.ProdSubquot.prod₂_isSubquotient k r t U A W B σ α ρ β hα hβ h₁ h₂).trans
      (.of_injective F.toIntertwiningMap F.toLinearEquiv.injective))

end GlobalTheory.CompanionTheory.Ysupp
