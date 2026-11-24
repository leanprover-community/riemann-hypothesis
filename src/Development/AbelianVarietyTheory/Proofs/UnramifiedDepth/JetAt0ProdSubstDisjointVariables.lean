module

public import Formalism.IncomingBounds.StatementThmP
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdRename
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.JetProdSubst

theorem jetAt0_prod_subst : ∀ (C : Type) [Field C] (Orb : Type) [Fintype Orb] (σ : Orb → Type) [∀ o, Fintype (σ o)] (τ : Type) (e : ∀ o, σ o → τ), Function.Injective (fun x : (Σ o, σ o) => e x.1 x.2) → ∀ (P : ∀ o, MvPolynomial (σ o) C) (F : ∀ o, MvPowerSeries (σ o) C), jetAt0 (∏ o, MvPolynomial.rename (e o) (P o)) (∏ o, MvPowerSeries.subst (fun x : σ o => (MvPowerSeries.X (e o x) : MvPowerSeries τ C)) (F o)) = ∏ o, jetAt0 (P o) (F o) := by
  intro C _ Orb _ σ _ τ e he P F
  let e' : ∀ o, σ o ↪ τ := fun o => ⟨e o, fun x y h => by
    have h1 : (⟨o, x⟩ : Σ o, σ o) = ⟨o, y⟩ := he h
    simpa using h1⟩
  have hd : ∀ i j x y, e' i x = e' j y → i = j := fun i j x y h =>
    congrArg Sigma.fst (he (a₁ := ⟨i, x⟩) (a₂ := ⟨j, y⟩) h)
  rw [← GlobalTheory.JetProd.jetAt0_prod_rename e' hd]
  congr 1
  refine Finset.prod_congr rfl fun o _ => ?_
  rw [MvPowerSeries.rename_eq_subst]
  rfl

end GlobalTheory.JetProdSubst
