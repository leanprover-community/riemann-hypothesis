module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
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

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def chN {m : ℕ} (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * t * (b * gramX ε u).trace)

def levF {m : ℕ} (e : ℤ) (a : Matrix (Fin n) (Fin n) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  a.det ^ e * (star a.det) ^ ((m : ℤ) - e) * f (Matrix.of u * a)

def vac {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) : (Fin m → Fin n → ℂ) → ℂ := gZf ε t c (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))

def TensInj : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ f g : (Fin V.rank → Fin n → ℂ) → ℂ,
    (∀ Ψ, AwayCls θ τ fr Ψ → tens θ τ fr f Ψ = tens θ τ fr g Ψ) → f = g

def LawN : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∀ (y : GR n) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b → mR y = nU b → ∀ f, IsSch f →
      L y f = fun u => chN ε (tLoc l τ) b u * f u

def LawM : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∃ e : ℤ, ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∀ f, IsSch f → L y f = levF e a f

def LawNbar : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∀ (y : GR n) (c : Matrix (Fin n) (Fin n) ℂ), cᴴ = c → mR y = nbar c → ∀ f, IsSch f →
      L y f = fun u => ((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ (2 * V.rank * n) *
        ftLoc ε (tLoc l τ) (fun v => chN ε (tLoc l τ) (-c) v * ftLoc ε (-tLoc l τ) f v) u

def VacK : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L → ∀ e : ℤ,
    (∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∀ f, IsSch f → L y f = levF e a f) →
    ∀ k : GR n, InK (mR k) → L k (vac ε (tLoc l τ) (cLoc l τ)) =
      fun u => jF e (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false) k (Complex.I • 1) *
        vac ε (tLoc l τ) (cLoc l τ) u

def IwaGR : Prop :=
  ∀ (n : ℕ) (y : GR n), ∃ p k : GR n, y = p * k ∧ (mR p).toBlocks₂₁ = 0 ∧ InK (mR k)

def SiegelOrb : Prop :=
  ∀ (n : ℕ) (Z : Matrix (Fin n) (Fin n) ℂ), IsSiegel Z → ∃ q : GR n, (mR q).toBlocks₂₁ = 0 ∧ actZ q (Complex.I • 1) = Z

def CocycleZ : Prop :=
  ∀ (n : ℕ) (e : ℤ) (p q : ℕ) (y y' : GR n) (Z : Matrix (Fin n) (Fin n) ℂ), IsSiegel Z →
    IsUnit ((mR y').toBlocks₂₁ * Z + (mR y').toBlocks₂₂).det ∧ IsUnit ((mR y').toBlocks₂₁ * Zᴴ + (mR y').toBlocks₂₂).det ∧
    IsSiegel (actZ y' Z) ∧ actZ (y * y') Z = actZ y (actZ y' Z) ∧ jF e p q (y * y') Z = jF e p q y (actZ y' Z) * jF e p q y' Z

def LocMul : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∀ (y y' : GR n) f, IsSch f → L (y * y') f = L y (L y' f)

end PositivityTheory.Rg.Sw.Glob
