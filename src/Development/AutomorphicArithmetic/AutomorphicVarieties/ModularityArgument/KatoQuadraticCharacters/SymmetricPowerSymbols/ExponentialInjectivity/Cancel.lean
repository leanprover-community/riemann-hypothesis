module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.IsSymb
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvEx
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.PC.cancel :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m → ∀ (τ τ' : X.K ≃+* X.K) (s s' : Ω ≃ₐ[ℚ] Ω), admitted X τ s → admitted X τ' s' →
        ∀ (u v : X.K) (P Q R : Pt X m), IsPt X m u v P → IsPt X m (τ u) (τ v) Q → IsPt X m (τ' (τ u)) (τ' (τ v)) R →
          ∀ f, Mv X m τ s P Q 1 → Mv X m (τ.trans τ') (s' * s) P R f → Mv X m τ' s' Q R f := by
  intro Ω _ _ _ ε X m hm τ τ' s s' hτ hτ' u v P Q R hP hQ hR f h1 hf
  obtain ⟨-, -, -, htr, -⟩ := admB Ω ε X
  obtain ⟨g, -, hg⟩ := (mvEx Ω ε X m hm τ' s' hτ' _ _ _ hQ).1 R hR
  have hc := mvComp Ω ε X m hm τ τ' s s' hτ hτ' u v P Q R hP hQ hR 1 g h1 hg
  rw [map_one, one_pow, one_mul] at hc
  have hfg := ((mvEx Ω ε X m hm (τ.trans τ') (s' * s) (htr τ s τ' s' hτ hτ') u v P hP).2.2.2 R hR g f hc).1 hf
  exact ((mvEx Ω ε X m hm τ' s' hτ' _ _ _ hQ).2.2.2 R hR g f hg).2 hfg
