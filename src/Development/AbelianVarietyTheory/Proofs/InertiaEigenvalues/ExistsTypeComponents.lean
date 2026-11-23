module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.TypeRec

theorem exists_isComp_of_rowDepth {D : D7} (I : Ident D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (h : GlobalTheory.HeightCounting.RowDepth D rep) : ∃ cp, IsComp I rep cp := by
  have : ∀ σ k v, ∃ c : GlobalTheory.GoodTypes.LocRep D k, ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (h : s.w = D.naut.plGw k v)
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) ((D.naut.plGw k v).adicCompletion D.host.E))),
    GlobalTheory.HeightCounting.IsLocS (rep σ).S s (h ▸ τ) ∧ c = pull I k v τ := by
    intro σ k v
    obtain ⟨s, τ, hs, h1, -⟩ := h σ k v
    have gen : ∀ (w) (e : s.w = w), ∃ τ' : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (w.adicCompletion D.host.E)),
        GlobalTheory.HeightCounting.IsLocS (rep σ).S s (e ▸ τ') := by
      rintro _ rfl
      exact ⟨τ, h1⟩
    obtain ⟨τ', a⟩ := gen _ hs
    exact ⟨_, s, hs, τ', a, rfl⟩
  choose c hc using this
  exact ⟨c, hc⟩

end GlobalTheory.TypeRec
