module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IsoVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.BdMul
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

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.isoJ :
    ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), IsoOk i → (∀ (V : Sig.Lev k) (V' : Sig.Lev k'), V.c = V'.c → (∀ a, Units.map (i : k →* k') a ∈ V'.H ↔ a ∈ V.H) → ∀ (n : ℕ) (g : GL (Fin n) k), GeneralLinearGroup.map (i : k →+* k') g ∈ V'.J n ↔ g ∈ V.J n) ∧ ∀ (n : ℕ) (g : GL (Fin n) k), GeneralLinearGroup.map (i : k →+* k') g ∈ KO k' (Fin n) ↔ g ∈ KO k (Fin n) := by
  intro k k' _ _ _ _ _ _ _ _ i hi
  obtain ⟨hv, hu, -, -⟩ := isoVal k k' i hi
  have hent : ∀ (n : ℕ) (g : GL (Fin n) k) (a b : Fin n),
      (GeneralLinearGroup.map (i : k →+* k') g : Matrix (Fin n) (Fin n) k') a b = i ((g : Matrix (Fin n) (Fin n) k) a b) := by
    intro n g a b
    rfl
  have h1 : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1 := hi.int
  refine ⟨?_, ?_⟩
  · intro V V' hc hH n g
    rw [Sig.memJ, Sig.memJ]
    simp only [hent, h1]
    have hpow : ∀ x : k, valuation k' (i x) ≤ valuation k' ↑(Hi.unif k') ^ (V'.c + 1) ↔
        valuation k x ≤ valuation k ↑(Hi.unif k) ^ (V.c + 1) := by
      intro x
      rw [← hu, hc, ← map_pow, ← map_pow, ← map_pow, hv]
    simp only [hpow]
    have hd : ∀ x : k, (∃ u ∈ V'.H, (u : k') = i x) ↔ (∃ u ∈ V.H, (u : k) = x) := by
      intro x
      constructor
      · rintro ⟨u, hu', he⟩
        refine ⟨Units.map (i.symm : k' →* k) u, ?_, ?_⟩
        · rw [← hH]
          convert hu'
          ext
          simp
        · simp [he]
      · rintro ⟨u, hu', he⟩
        refine ⟨Units.map (i : k →* k') u, (hH u).2 hu', ?_⟩
        simp [he]
    simp only [hd]
  · intro n g
    rw [Hi.GlAx.mem_KO, Hi.GlAx.mem_KO, Hi.GlAx.bd_zero, Hi.GlAx.bd_zero, Hi.GlAx.bd_zero, Hi.GlAx.bd_zero,
      ← map_inv]
    exact and_congr (forall_congr' fun a => forall_congr' fun b => h1 _)
      (forall_congr' fun a => forall_congr' fun b => h1 _)
