module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypePS2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LaArtin
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




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.J.D
private def resEquiv {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} (K : Subgroup G) (e : ρ.Equiv ρ') :
    Representation.Equiv (ρ.comp K.subtype) (ρ'.comp K.subtype) :=
  Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v =>
    Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (g : G) v
theorem resEq2_alt : _root_.UpperTheory.V.Z.J.D.TypePS2Alt → PsRes → _root_.UpperTheory.V.Z.J.D.ResidualEqualityRankTwo := by
  intro hT hP hN L Ω _ _ _ _ _ _ n hn π π' w A h τ τ' hτ hτ' χ hx hc hc'
  obtain ⟨ω, hs, ⟨e⟩, hω⟩ := hT hN L Ω n hn π w A h τ hτ χ hx hc
  obtain ⟨ω', hs', ⟨e'⟩, hω'⟩ := hT hN L Ω n hn π' w A h τ' hτ' χ hx hc'
  have ha : IsLocalArtin h (artOf h) := Classical.epsilon_spec (_root_.UpperTheory.V.Z.Win.T2.laArtinLit' hN h)
  have hu : ∀ i (y : Uo (w.adicCompletion L)), ω i y = ω' i y := by
    intro i y
    obtain ⟨σ, hσ⟩ := ha.surj y
    have h1 : valuation (w.adicCompletion L) (artOf h σ : w.adicCompletion L) = 1 := by
      rw [hσ]
      exact y.2
    have h2 := ha.ord_eq σ
    rw [GlobalTheory.SmGL.ord_eq_zero_iff.2 h1] at h2
    have hI : (σ : G L Ω) ∈ Ine (F := L) A := deg_eq_zero_iff.mp (by omega)
    have e1 : artOf h (ineIncl h ⟨σ, hI⟩) = y := hσ
    have h3 := hω i ⟨σ, hI⟩
    have h4 := hω' i ⟨σ, hI⟩
    rw [e1] at h3 h4
    exact h3.trans h4.symm
  obtain ⟨f⟩ := hP (w.adicCompletion L) n ω ω' hs hs' hu
  exact ⟨(resEquiv _ e).trans (f.trans (resEquiv _ e').symm)⟩
end UpperTheory.V.Z.J.D
end
end
