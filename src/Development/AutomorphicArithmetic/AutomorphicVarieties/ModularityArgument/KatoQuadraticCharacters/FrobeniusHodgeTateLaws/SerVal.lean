module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CoPtMu
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart

@[expose] public section

noncomputable section

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.EisM GlobalTheory.KummerEisensteinGalois

namespace UpperTheory.V.Z.Kato.Joint

def ser {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N : ℕ) [NeZero N] (θ : DirichletCharacter ℂ N) (m k : ℕ)
    (ψ : DirichletCharacter (PadicAlgCl l) (l ^ m)) (a b : ℤ) : ℕ → PadicAlgCl l :=
  up (l ^ m) fun i => ∑ x : ZMod N, ι.symm (hat θ (x.val : ℤ) / 2) * coPtMu N l m k ψ ((x.val : ℤ) * a) b i

def frm (l N m k : ℕ) (θ ν : DirichletCharacter ℂ N) (f : ZMod (l ^ m) → ℂ) : ℕ → ℂ :=
  (Uo l)^[m] (Zm k l (hat θ) (ch ν) fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))

def AvgEq : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N : ℕ) [NeZero N] (θ χ : DirichletCharacter ℂ N) (m k : ℕ)
    (ψ : DirichletCharacter (PadicAlgCl l) (l ^ m)) (a b : ℤ), l ≠ 2 → 1 ≤ m → 3 ≤ k → Odd k → χ (-1) = -1 → IsCoprime a N → IsCoprime b N →
    (ι (ψ (-1)) ≠ θ (-1) → ser ι N θ m k ψ a b = 0) ∧
    (∀ a' b' : ℤ, a ≡ a' [ZMOD N] → b ≡ b' [ZMOD N] → ser ι N θ m k ψ a b = ser ι N θ m k ψ a' b') ∧
    (ι (ψ (-1)) = θ (-1) → ∀ i, ∑ u : (ZMod N)ˣ, χ u * ι (ser ι N θ m k ψ (((u : ZMod N).val : ℤ) * a) (((u : ZMod N).val : ℤ) * b) i) =
      2 * θ (a : ZMod N) * (θ * χ)⁻¹ (b : ZMod N) * frm l N m k θ (θ * χ) (fun y => ι (ψ y)) i)

def AvgMF : Prop :=
  ∀ (k l N m : ℕ) (θ χ : DirichletCharacter ℂ N) (f : ZMod (l ^ m) → ℂ) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ), l.Prime → 3 ≤ k → Odd k →
    0 < N → ¬ l ∣ N → 1 ≤ m → χ (-1) = -1 → (∀ y, f (-y) = θ (-1) * f y) → α ≠ 0 → EigAll k N l χ t α B c →
    MF k (N * l) (ch χ) (frm l N m k θ (θ * χ) f) ∧
      2 * lam B c (frm l N m k θ (θ * χ) f) = (N.totient : ℂ) * α ^ m * mesMu k l (hat θ) (tw2 N (θ (-1))) α B c m f

end UpperTheory.V.Z.Kato.Joint

end
