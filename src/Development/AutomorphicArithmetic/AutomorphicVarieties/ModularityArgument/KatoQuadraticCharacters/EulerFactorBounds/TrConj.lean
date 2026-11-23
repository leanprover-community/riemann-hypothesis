module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.WkTopEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

namespace UpperTheory.V.Z.Kato.Nb.TrConj

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem cast_down {M K : ℕ} (h : K ∣ M) {a b : ℤ} (e : (a : ZMod M) = b) : (a : ZMod K) = b := by
  have e' := congrArg (ZMod.castHom h (ZMod K)) e
  rwa [map_intCast, map_intCast] at e'

theorem gamma_le {M K : ℕ} (h : K ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma K := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using cast_down h (b := 1) (by simpa using h1)
  · simpa using cast_down h (b := 0) (by simpa using h2)
  · simpa using cast_down h (b := 0) (by simpa using h3)
  · simpa using cast_down h (b := 1) (by simpa using h4)

theorem slU_mul (X : Tower Ω ε) (γ γ' : SL(2, ℤ)) (a : X.Kˣ) :
    slU X (ofSL (γ * γ')) a = slU X (ofSL γ') (slU X (ofSL γ) a) := by
  ext
  show X.sl (ofSL (γ * γ')) (a : X.K) = X.sl (ofSL γ') (X.sl (ofSL γ) (a : X.K))
  rw [map_mul, X.sl_mul]

theorem cgr_map {K : Type} [Field K] {m : ℕ} (φ : Kˣ →* Kˣ) {a b : Kˣ} (h : Cgr m a b) : Cgr m (φ a) (φ b) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨φ k, by rw [map_mul, map_pow]⟩

end

end UpperTheory.V.Z.Kato.Nb.TrConj
