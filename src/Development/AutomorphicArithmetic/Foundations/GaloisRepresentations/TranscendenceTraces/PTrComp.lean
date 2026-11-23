module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trComp_of :
    TrChar → FamComp → WtComp → RpBasic → RpOp → TrComp := by
  intro hChar hFam hWc hRp hOp q _ n i W Z S r p _ _ w' w hr hp hq x
  have hrp : IsWt (r ≫ p) (Wt.mul r w' w) := hWc r p w' w hr hp
  have hqZ : IsUnit ((q : ℕ) : Γ(Z, ⊤)) := by
    have := hq.map p.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨_, hsr, _⟩ := hChar q i r w' hr hqZ
  obtain ⟨_, hsp, _⟩ := hChar q i p w hp hq
  obtain ⟨σ, hσ, hσeq⟩ := hFam q i r p w' w (trFam r w' q i) (trFam p w q i) hsr hsp
  rw [(hChar q i (r ≫ p) _ hrp hq).2.2 σ hσ n, (hChar q i p w hp hq).2.2 _ hsp n,
    (hChar q i r w' hr hqZ).2.2 _ hsr n]
  obtain ⟨a, ha⟩ := (hRp (ZMod q) (res (ZMod q) (tw q i)) W n).1 x
  have h1 := hOp _ _ (trFam r w' q i) n x a ha
  have h2 := hOp _ _ (trFam p w q i) n _ _ h1
  have h3 := hOp _ _ σ n x a ha
  rw [hσeq n a] at h3
  exact ((hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1 _ _ _ _ h3 h2).2.1 rfl
