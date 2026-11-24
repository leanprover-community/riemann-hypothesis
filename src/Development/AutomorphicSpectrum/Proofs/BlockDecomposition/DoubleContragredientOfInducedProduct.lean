module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ContraProd

theorem contra_contra_of_equiv {G V W U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    {σ : Representation ℂ G V} {τ : Representation ℂ G W} {υ : Representation ℂ G U}
    (E₁ : (contra σ).Equiv τ) (E₂ : (contra τ).Equiv υ) (E₃ : υ.Equiv σ) :
    Nonempty ((contra (contra σ)).Equiv σ) :=
  ⟨((GlobalTheory.ContraRefl.contraEquiv E₁).symm.trans E₂).trans E₃⟩

theorem prodIrr_equiv_of_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} {x y : Fin h → IrrGL (k := k)} (e : y = x)
    (hy : ∑ a, (y a).1 = N) (hx : ∑ a, (x a).1 = N) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr x hx)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem contra_contra_prodIrr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Nonempty ((contra (contra (prodIrr x hd))).Equiv (prodIrr x hd)) := by
  intro k _ _ _ _ hA h N x hd
  refine Exists.elim (contra_prodIrr hA x hd) fun hd₁ H₁ => H₁.elim fun E₁ => ?_
  refine Exists.elim (contra_prodIrr hA (fun a => Zc.dualCl (x a)) hd₁) fun hd₂ H₂ => H₂.elim fun E₂ => ?_
  refine (prodIrr_equiv_of_eq (funext fun a => GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA (x a)) hd₂ hd).elim fun E₃ => ?_
  exact contra_contra_of_equiv E₁ E₂ E₃

end GlobalTheory.CompanionTheory.ContraProd

end
