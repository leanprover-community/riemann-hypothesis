module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel
open GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.N3

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

abbrev iP (ξ : Fin n → ℂˣ) := prinSeries (k := k) (n := Fin n) fun i => unrChar k (ξ i)

def IsExpN {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ξ : Fin n → ℂˣ) : Prop :=
  ∃ ℓ : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧
    ∀ t v, ℓ (jacB π t v) = (torusChar (fun i => unrChar k (ξ i)) t : ℂ) * ℓ v

def Mono (ξ : Fin n → ℂˣ) : Prop := ∀ i j : Fin n, i ≤ j → ‖(ξ j : ℂ)‖ ≤ ‖(ξ i : ℂ)‖

variable (k)

def ExpEmb : Prop := ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
  (ξ : Fin n → ℂˣ), IsSmooth π → IsExpN π ξ →
  ∃ f : π.IntertwiningMap (iP (k := k) ξ), f ≠ 0

def SphEmb : Prop := ∀ (n : ℕ) (ξ : Fin n → ℂˣ), Mono ξ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible → IsSpherical π →
  IsSubquotient π (iP (k := k) ξ) → ∃ f : π.IntertwiningMap (iP (k := k) ξ), Function.Injective f

def UniqSub : Prop := CharZero k → ∀ (n : ℕ) (ξ : Fin n → ℂˣ), Mono ξ → ∀ (V W : Type) [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) k) V) (σ : Representation ℂ (GL (Fin n) k) W),
  π.IsIrreducible → σ.IsIrreducible → ∀ (f : π.IntertwiningMap (iP (k := k) ξ)) (g : σ.IntertwiningMap (iP (k := k) ξ)),
    f ≠ 0 → g ≠ 0 → Nonempty (π.Equiv σ)

def SphConst : Prop := ∀ (n : ℕ) (ξ : Fin n → ℂˣ), ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
  (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π ∧ π.IsIrreducible ∧ IsSpherical π ∧ IsSubquotient π (iP (k := k) ξ)

def ExtremeSph : Prop := CharZero k → ∀ (n : ℕ) (ξ : Fin n → ℂˣ), Mono ξ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible →
  (∃ f : π.IntertwiningMap (iP (k := k) ξ), f ≠ 0) → IsSpherical π

end Local

section Global

variable {E : Type} [Field E] [NumberField E] {c n : ℕ} {N : Fin c → ℕ}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def N3 : Prop := ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (c n : ℕ) (N : Fin c → ℕ)
  (h : ∑ i, N i = n) (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))) (P : SmIrr (GL (Fin n) (w.adicCompletion E)))
  (ξ : Fin n → ℂˣ), IsSubquotient P.ρ (locProd h w σ) → IsExpN P.ρ ξ → Mono ξ →
  (∀ i, GlobalTheory.LGrp.IsSpherical (σ i).ρ (GlobalTheory.LFun.KGL w (n := (N i)))) ∧
    ∃ b : Fin c → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL w (σ i).ρ (b i)) ∧ ∑ i, b i = Finset.univ.val.map ξ

def SatLink : Prop := ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (c n : ℕ) (N : Fin c → ℕ)
  (h : ∑ i, N i = n) (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))) (P : SmIrr (GL (Fin n) (w.adicCompletion E)))
  (ξ : Fin n → ℂˣ), IsSubquotient P.ρ (locProd h w σ) → IsSpherical P.ρ →
  (∃ f : P.ρ.IntertwiningMap (iP (k := w.adicCompletion E) ξ), f ≠ 0) →
  (∀ i, GlobalTheory.LGrp.IsSpherical (σ i).ρ (GlobalTheory.LFun.KGL w (n := (N i)))) ∧
    ∃ b : Fin c → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL w (σ i).ρ (b i)) ∧ ∑ i, b i = Finset.univ.val.map ξ

end Global

end PositivityTheory.Rg.BcB.N3

end
