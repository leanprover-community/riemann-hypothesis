module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesConjOfAdm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
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

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain

namespace GlobalTheory.TypeRec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local instance factG (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

structure Ident (D : D7) where
  i : ∀ (k : Fin 2) (v : D.nd.PlG k), ℚ_[D.host.g k] ≃+* (D.naut.plGw k v).adicCompletion D.host.E
  cont : ∀ k v, Continuous (i k v)

def pull {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E))) :
    Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k]) :=
  Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom))

def IsRc (hL : GlobalTheory.Published.LocalLanglandsGL) {D : D7} (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D)
    (rc : GlobalTheory.SerSys.Corr D) : Prop :=
  ∀ k v n (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)))
    (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k])), Nonempty (π ≅ pull I k v σ) →
    T.e _ (rc k v n π) = GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 (D.naut.plGw k v)) (GlobalTheory.LocLanglands.cls σ)

def IsComp {D : D7} (I : Ident D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (cp : GlobalTheory.GoodTypes.Comp D) : Prop :=
  ∀ σ k v, ∃ (s : SplitPlace D.host.E) (h : s.w = D.naut.plGw k v)
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) ((D.naut.plGw k v).adicCompletion D.host.E))),
    GlobalTheory.HeightCounting.IsLocS (rep σ).S s (h ▸ τ) ∧ cp σ k v = pull I k v τ

end GlobalTheory.TypeRec

end
