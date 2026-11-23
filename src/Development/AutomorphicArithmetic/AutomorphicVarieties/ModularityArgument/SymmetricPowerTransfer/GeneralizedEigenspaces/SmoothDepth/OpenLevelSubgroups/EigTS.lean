module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.eigTS :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (V : Type) [AddCommGroup V] [Module ℂ V] (φ : UA L 2 → V) (w : Plc L) (W : Sig.Lev (Kw w)) (ψ : Fin 2 → (Kw w)ˣ →* ℂˣ), EigT φ w W ψ → EigS φ w W (ψ 0 / ψ 1) := by
  intro L _ _ _ V _ _ φ w W ψ h t ht
  have hd : Sig.SDom ![t, t⁻¹] := by
    intro i j hij
    have h0 : valuation (Kw w) (t : Kw w) ≠ 0 := by simp
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    exact ht.trans ((one_lt_inv₀ (zero_lt_iff.2 h0)).2 ht)
  have e : Dict.expo ![ψ 0 / ψ 1, 1] ![t, t⁻¹] = Dict.expo ψ ![t, t⁻¹] := by
    simp [Dict.expo, torusChar, Fin.prod_univ_two, div_eq_mul_inv]
  rw [e]; exact h _ hd
